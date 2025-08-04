require "set"
require "parcopy"

module Regalloc
  module DSL
    def cmp *ins
      self << Insn.new(:cmp, nil, ins)
    end

    def mul a, b
      out = func.next_vreg
      self << Insn.new(:mul, out, [a, b])
      out
    end

    def sub a, b
      out = func.next_vreg
      self << Insn.new(:sub, out, [a, b])
      out
    end

    def add a, b
      out = func.next_vreg
      self << Insn.new(:add, out, [a, b])
      out
    end

    def ret innie
      self << Insn.new(:ret, nil, [innie])
    end

    def loadi imm
      raise unless imm.is_a? Immediate
      out = func.next_vreg
      self << Insn.new(:loadi, out, [imm])
      out
    end

    def imm v
      Immediate.new v
    end

    def edge block, args = []
      Edge.new(block, args)
    end

    def blt iftrue:, iffalse:
      self << Insn.new(:blt, nil, [iftrue, iffalse])
    end

    def jump edge
      self << Insn.new(:jump, nil, [edge])
    end

    def define(*block_params, &blk)
      self.parameters.concat(block_params)
      self.instance_eval(&blk)
    end
  end

  class Interval
    attr_reader :range

    def initialize
      @range = nil
    end

    def add_range(from, to)
      if to <= from
        raise ArgumentError, "Invalid range: #{from} to #{to}"
      end
      if !@range
        @range = Range.new(from, to)
        return
      end
      @range = Range.new([@range.begin, from].min, [@range.end, to].max)
    end

    def set_from(from)
      @range = if @range
        Range.new(from, @range.end)
      else
        # This happens when we don't have a use of the vreg
        Range.new(from, from)
      end
    end

    def inspect
      if @range
        "Range(#{@range.begin}, #{@range.end})"
      else
        "Range(nil, nil)"
      end
    end

    def ==(other)
      other.is_a?(Interval) && @range == other.range
    end
  end

  class Function
    attr_accessor :entry_block
    attr_reader :instructions

    def initialize
      @next_vreg_name = 10
      @next_blk_name = 1
      @vregs = {}
      @block_order = nil
    end

    def number_instructions!
      @block_order = rpo
      number = 16
      @block_order.each do |blk|
        blk.number = number
        number += 2
        blk.instructions.each do |insn|
          insn.number = number
          number += 2
        end
        blk.to = number
      end
    end

    # TODO(max): Handle calls.
    # We need to do register move/hint stuff for parameters and return
    # We need to do spilling of live-across vregs ("survivors")

    def build_intervals live_in
      intervals = Hash.new { |hash, key| hash[key] = Interval.new }
      @block_order.each do |block|
        # live = union of successor.liveIn for each successor of b
        live = block.successors.map { |succ| live_in[succ] }.reduce(0, :|)
        # for each phi function phi of successors of b do
        #   live.add(phi.inputOf(b))
        live |= block.out_vregs.map { |vreg| 1 << vreg.num }.reduce(0, :|)
        each_bit(live) do |idx|
          opd = vreg idx
          intervals[opd].add_range(block.from, block.to)
        end
        block.instructions.reverse.each do |insn|
          out = insn.out&.as_vreg
          if out
            # for each output operand opd of op do
            #   intervals[opd].setFrom(op.id)
            intervals[out].set_from(insn.number)
          end
          # for each input operand opd of op do
          #   intervals[opd].addRange(b.from, op.id)
          insn.vreg_ins.each do |opd|
            intervals[opd].add_range(block.from, insn.number)
          end
        end
      end
      intervals
    end

    def ye_olde_linear_scan intervals, num_registers
      if num_registers <= 0
        raise ArgumentError, "Number of registers must be positive"
      end
      # TODO(max): Use a bitset in Rust
      free_registers = Set.new 0...num_registers
      # Aaron wants to call this "ActiveStorage" >:( >:( >:(
      active = []  # Active intervals, sorted by increasing end point
      assignment = {}  # Map from Interval to PReg|StackSlot
      num_stack_slots = 0
      # Iterate through intervals in order of increasing start point
      intervals.sort_by { |_, interval| interval.range.begin }.each do |_vreg, interval|
        # expire_old_intervals(interval)
        # TODO(max): We can probably do this slightly faster by starting at the
        # current interval's start point index in active and walking backwards?
        # Maybe?
        active.select! do |active_interval|
          if active_interval.range.end >= interval.range.begin
            true
          else
            operand = assignment.fetch(active_interval)
            raise "Should be assigned a register" unless operand.is_a?(PReg)
            free_registers.add(operand.name)
            false
          end
        end
        if active.length == num_registers
          # spill_at_interval(interval)
          # Pick an interval to spill. Picking the longest-lived active one is
          # a heuristic from the original linear scan paper.
          spill = active.last
          # In either case, we need to allocate a slot on the stack.
          # TODO(max): Reuse freed stack slots
          # TODO(max): Insert a spill instruction at an odd index
          slot = StackSlot.new(num_stack_slots)
          num_stack_slots += 1
          if spill.range.end > interval.range.end
            # The last active interval ends further away than the current
            # interval; spill the last active interval.
            assignment[interval] = assignment[spill]
            raise "Should be assigned a register" unless assignment[interval].is_a?(PReg)
            assignment[spill] = slot
            active.pop  # We know spill is the last one
            # Insert interval into already-sorted active
            insert_idx = active.bsearch_index { |i| i.range.end >= interval.range.end } || active.length
            active.insert(insert_idx, interval)
          else
            # The current interval ends further away than the last active
            # interval; spill the current interval.
            assignment[interval] = slot
          end
        else
          # TODO(max): Use ctz to get lowest free register
          reg = free_registers.min
          free_registers.delete(reg)
          assignment[interval] = PReg.new(reg)
          # Insert interval into already-sorted active
          insert_idx = active.bsearch_index { |i| i.range.end >= interval.range.end } || active.length
          active.insert(insert_idx, interval)
        end
      end
      [assignment, num_stack_slots]
    end

    def resolve_ssa intervals, assignments
      num_predecessors = Hash.new 0
      @block_order.each do |block|
        block.edges.each do |edge|
          num_predecessors[edge.block] += 1
        end
      end
      replacement_opnd = -> (opnd) { assignments[intervals[opnd]] }
      @block_order.each do |predecessor|
        predecessor.instructions.each do |insn|
          out = replacement_opnd.(insn.out)
          if out
            insn.out = out
          end
          insn.ins.map! do |innie|
            replacement_opnd.(innie) || innie
          end
        end
        outgoing_edges = predecessor.edges
        num_successors = outgoing_edges.length
        outgoing_edges.each do |edge|
          mapping = []
          # We don't do interval splitting, so intervals are either in one
          # place for the whole time (not a thing we need to generate a move
          # for) or we are doing an inter-block argument->parameter move.
          #
          # Therefore, we only need to find intervals that start at the
          # beginning of the successor, AKA block params.
          successor = edge.block
          edge.args.zip(successor.parameters).each do |src, dst|
            moveFrom = if src.is_a?(Immediate)
                         src
                       else
                         assignments[intervals[src]]
                       end
            moveTo = assignments[intervals[dst]]
            if moveFrom != moveTo
              mapping << [moveFrom, moveTo]
            end
          end
          # predecessor.order_and_insert_moves(mapping)
          sequence = sequentialize(mapping).map do |(src, _, dst)|
            Insn.new(:mov, dst, [src])
          end
          # If we don't have any moves to insert, we don't have any block to
          # insert
          next if sequence.empty?
          if num_predecessors[successor] > 1 && num_successors > 1
            # TODO(max): Figure out a move sequence that actually causes a critical edge split
            raise "????????"
            b = new_block
            b.insert_moves_at_start sequence
            b.instructions << Insn.new(:jump, nil, [Edge.new(successor, [])])
            edge.block = b
          elsif num_successors > 1
            # Insert into the beginning of the block
            # raise "May not happen??????"
            successor.insert_moves_at_start sequence
          else
            # Insert into the end of the block... before the terminator
            predecessor.insert_moves_at_end sequence
          end
          # TODO(max): Rewrite vregs to pregs
        end
      end
      # Remove all block parameters and arguments; we have resolved SSA
      @block_order.each do |block|
        block.parameters.clear
        block.edges.each do |edge|
          edge.args.clear
        end
      end
      # TODO(max): Recalculate @block_order since we inserted new splitting
      # blocks
    end

    def rpo
      po.reverse
    end

    def po
      entry_block.po_traversal(Set.new, [])
    end

    def next_vreg
      vreg = VReg.new @next_vreg_name
      @vregs[@next_vreg_name] = vreg
      @next_vreg_name += 1
      vreg
    end

    def vreg idx
      @vregs[idx]
    end

    def new_block
      blk = Block.new(self, @next_blk_name, [], [])
      @next_blk_name += 1
      blk
    end

    def pretty_print(pp)
      pp.text "Function:"
      pp.breakable
      rpo.each_with_index do |block, i|
        pp.text "#{block.number}: " if block.number
        pp.breakable if i > 0
        pp.text "  #{block.name}:"
        if block.parameters.any?
          pp.text " (#{block.parameters.map(&:inspect).join(", ")})"
        end
        pp.breakable
        block.instructions.each do |insn|
          pp.text "    "
          insn.pretty_print(pp)
          pp.breakable
        end
      end
    end

    def graphviz
      result = "digraph G {\n"
      result << <<~END
       node [shape=plaintext]
      END
      rpo.each do |block|
        result << <<~END
          #{block.name} [label=<<TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
        END
        params = block.parameters.map(&:inspect).join(", ")
        result << <<~END
          <TR><TD PORT="params" BGCOLOR="gray">#{block.name}(#{params})&nbsp;</TD></TR>
        END
        block.instructions.each_with_index do |insn, idx|
          out = if insn.out
                  "#{insn.out.inspect} = "
                else
                  ""
                end
          ins = insn.ins.map(&:inspect).join(", ")
          result << <<~END
            <TR><TD ALIGN="left" PORT="#{idx}">#{out}#{insn.name} #{ins}&nbsp;</TD></TR>
          END
        end
        result << <<~END
          </TABLE>>];
        END
        last_index = block.instructions.length - 1
        block.successors.each do |succ|
          result << "#{block.name}:#{last_index} -> #{succ.name}:params;\n"
        end
      end
      result << "}"
      result
    end

    def compute_initial_liveness_sets order
      gen = Hash.new 0
      kill = Hash.new 0
      order.each do |block|
        block.instructions.reverse_each do |insn|
          out = insn.out&.as_vreg
          if out
            kill[block] |= (1 << out.num)
          end
          insn.vreg_ins.each do |vreg|
            gen[block] |= (1 << vreg.num)
          end
        end
        block.parameters.each do |param|
          kill[block] |= (1 << param.num)
        end
      end
      [gen, kill]
    end

    def analyze_liveness
      # Map from Block to bitset of VRegs live at entry
      order = po
      gen, kill = compute_initial_liveness_sets(order)
      live_in = Hash.new 0
      changed = true
      while changed
        changed = false
        for block in order
          block_live = block.successors.map { |succ| live_in[succ] }.reduce(0, :|)
          block_live |= gen[block]
          block_live &= ~kill[block]
          if live_in[block] != block_live
            changed = true
            live_in[block] = block_live
          end
        end
      end
      live_in
    end
  end

  class Block
    include DSL

    attr_reader :instructions
    attr_reader :parameters
    attr_reader :func
    attr_accessor :number, :to
    alias :from :number

    def initialize func, idx, insns, parameters
      @func = func
      @instructions = insns
      @parameters = parameters
      @idx = idx
    end

    def name
      "B#{@idx}"
    end

    def << insn
      @instructions << insn
    end

    def edges
      @instructions.last.dests
    end

    def successors
      edges.map(&:block)
    end

    def out_vregs
      @instructions.last.dests.map(&:args).reduce([], :+).grep(VReg)
    end

    def po_traversal visited, post_order
      return post_order if visited.include?(self)

      visited.add(self)

      successors.each do |successor|
        successor.po_traversal(visited, post_order)
      end

      post_order << self
      post_order
    end

    def insert_moves_at_start moves
      @instructions.unshift *moves
    end

    def insert_moves_at_end moves
      # Insert before the terminator (at -1)
      @instructions.insert(-2, *moves)
    end
  end

  class Insn
    attr_reader :name, :ins
    attr_accessor :id, :number, :out

    def initialize name, out, ins
      @name = name
      @out = out
      @ins = ins
      @number = nil
    end

    def pretty_print(pp)
      pp.text "#{@number}: " if @number
      if @out
        pp.text "#{@out.inspect} = "
      end
      pp.text @name.to_s
      if @ins && @ins.any?
        pp.text " "
        if @name == :blt
          pp.text "iftrue: #{@ins[0].inspect}, iffalse: #{@ins[1].inspect}"
        else
          pp.text @ins.map(&:inspect).join(", ")
        end
      end
    end

    def dests
      ins.grep(Edge)
    end

    def vreg_ins
      result = []
      ins.each do |op|
        if op.is_a?(VReg)
          result << op
        elsif op.is_a?(Edge)
          result.concat(op.args.grep(VReg))
        end
      end
      result
    end
  end

  class Operand
    def pretty_print(pp)
      pp.text inspect
    end

    def as_vreg = nil
  end

  class Immediate < Operand
    attr_reader :val

    def initialize val
      @val = val
    end

    def inspect
      "$" + val.inspect
    end
  end

  class VReg      < Operand
    attr_reader :num
    def initialize num
      @num = num
    end

    def inspect
      "V#{@num}"
    end

    def as_vreg = self
  end

  class PReg      < Operand
    attr_reader :name

    def initialize name
      @name = name
    end

    def inspect
      "P#{@name}"
    end

    def == other
      other.is_a?(PReg) && @name == other.name
    end
  end

  class StackSlot < Operand
    attr_reader :index

    def initialize index
      @index = index
    end

    def inspect
      "Stack[#{@index}]"
    end

    def == other
      other.is_a?(StackSlot) && @index == other.index
    end
  end

  class Mem       < Operand
    attr_reader :base, :offset

    def initialize base, offset = 0
      @base = base
      @offset = offset
    end

    def inspect
      if @offset == 0
        "[#{@base.inspect}]"
      elsif @offset < 0
        "[#{@base.inspect} - #{@offset.abs}]"
      else
        "[#{@base.inspect} + #{@offset}]"
      end
    end
  end

  class Edge     < Operand
    attr_reader :args
    attr_accessor :block

    def initialize block, args
      raise unless block
      @block = block
      @args = args
    end

    def inspect
      block_name = @block.name
      if @args.empty?
        "→#{block_name}"
      else
        "→#{block_name}(#{@args.map(&:inspect).join(", ")})"
      end
    end
  end
end
