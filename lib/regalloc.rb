require "set"
require "parcopy"

def each_bit n
  idx = 0
  while n > 0
    if n & 1 == 1
      yield idx
    end
    idx += 1
    n >>= 1
  end
end

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

    def call args
      out = func.next_vreg
      self << Insn.new(:call, out, args)
      out
    end

    def add a, b
      out = func.next_vreg
      self << Insn.new(:add, out, [a, b])
      out
    end

    def mov(a) = add a, imm(0)

    def ret innie
      self << Insn.new(:ret, nil, [innie])
    end

    def loadi imm
      raise unless imm.is_a? Immediate
      out = func.next_vreg
      self << Insn.new(:loadi, out, [imm])
      out
    end

    def imm(v) = Immediate.new v

    def edge(block, args = []) = Edge.new(block, args)

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

    def survives?(x)
      raise unless @range
      range.begin < x && range.end > x
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
      # @range is nil when we don't have a use of the vreg
      @range = Range.new(from, @range&.end || from)
    end

    def inspect = "Range(#{@range&.begin}, #{@range&.end})"

    def ==(other)
      other.is_a?(Interval) && @range == other.range
    end
  end

  class Function
    attr_accessor :entry_block
    attr_accessor :next_vreg_name
    attr_accessor :insn_start_number

    def initialize
      @next_vreg_name = 10
      @next_blk_name = 1
      @vregs = {}
      @block_order = nil
      @insn_start_number = 16
    end

    def instructions = @block_order.flat_map(&:instructions)

    def number_instructions!
      @block_order = rpo
      number = insn_start_number
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
        # TODO(max): We can probably do this slightly faster by starting at the
        # current interval's start point index in active and walking backwards?
        # Maybe?
        # expire_old_intervals(interval)
        active.select! do |active_interval|
          if active_interval.range.end > interval.range.begin
            true
          else
            operand = assignment.fetch(active_interval)
            raise "Should be assigned a register" unless operand.is_a?(PReg)
            raise "Should have a name" unless operand.name
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
          reg = free_registers.min || raise("no free regs?")
          free_registers.delete(reg)
          assignment[interval] = PReg.new(reg)
          # Insert interval into already-sorted active
          insert_idx = active.bsearch_index { |i| i.range.end >= interval.range.end } || active.length
          active.insert(insert_idx, interval)
        end
      end
      [assignment, num_stack_slots]
    end

    def handle_caller_saved_regs intervals, assignments, return_reg, param_regs
      # TODO(max): Handle argument to `ret` instruction (which should always be in `return_reg`)
      @block_order.each do |block|
        x = block.instructions.flat_map do |insn|
          if insn.name == :call
            survivors = intervals.select { |x, r| r.survives?(insn.number) }.map(&:first).select { |vreg|
              assignments[intervals[vreg]].is_a?(PReg)
            }
            mov_input = insn.out
            insn.out = return_reg

            ins = insn.ins.drop(1)
            raise if ins.length > param_regs.length

            insn.ins.replace(insn.ins.first(1))

            sequence = sequentialize(ins.zip(param_regs).to_h).map do |(src, _, dst)|
              Insn.new(:mov, dst, [src])
            end

            # TODO(max): Align the stack
            survivors.map { |s| Insn.new(:push, nil, [s]) } +
              # sequentialize parameters
              # TODO(max): Don't write a mov when mov_input ends up in return_reg naturally
              sequence + [insn, Insn.new(:mov, mov_input, [return_reg])] +
              survivors.map { |s| Insn.new(:pop, nil, [s]) }.reverse
          else
            insn
          end
        end
        block.instructions.replace(x)
      end
    end

    def resolve_ssa intervals, assignments, param_regs
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
            # Make a new interstitial block
            b = new_block
            b.insert_moves_at_start sequence
            b.instructions << Insn.new(:jump, nil, [Edge.new(successor, [])])
            edge.block = b
          elsif num_successors > 1
            # Insert into the beginning of the block
            successor.insert_moves_at_start sequence
          else
            # Insert into the end of the block... before the terminator
            predecessor.insert_moves_at_end sequence
          end
        end
      end
      # Remove all block parameters and arguments; we have resolved SSA
      @block_order.each do |block|
        if block == entry_block
          block.parameters.map!(&replacement_opnd)
        else
          block.parameters.clear
        end
        block.edges.each do |edge|
          edge.args.clear
        end
      end

      # We're typically going to have more param regs than block parameters
      # When we zip the param regs with block params, we'll end up with param
      # regs mapping to nil. We filter those away by selecting for tuples
      # that have a truthy second value
      # [[x, y], [z, nil]].select(&:last) (reject the second tuple)
      sequence = sequentialize(param_regs.zip(entry_block.parameters).select(&:last).to_h).map do |(src, _, dst)|
        Insn.new(:mov, dst, [src])
      end

      entry_block.insert_moves_at_start(sequence)

      # TODO(max): Recalculate @block_order since we inserted new splitting
      # blocks
      # TODO(max): Split critical edges earlier so we don't have to recalculate
      # block_order
    end

    def rpo = po.reverse

    def po = entry_block.po_traversal(Set.new, [])

    def next_vreg
      vreg = VReg.new @next_vreg_name
      @vregs[@next_vreg_name] = vreg
      @next_vreg_name += 1
      vreg
    end

    def vreg(idx) = @vregs[idx]

    def new_block
      blk = Block.new(self, @next_blk_name, [], [])
      @next_blk_name += 1
      blk
    end

    def pretty_print(pp)
      pp.text "Function:"
      pp.text "\n"
      rpo.each_with_index do |block, i|
        if block.number
          pp.text "    "
          pp.text "#{block.number}: "
        end
        pp.breakable if i > 0
        pp.text "#{block.name}:"
        if block.parameters.any?
          pp.text " (#{block.parameters.map(&:inspect).join(", ")})"
        end
        pp.text "\n"
        block.instructions.each do |insn|
          pp.text "    "
          insn.pretty_print(pp)
          pp.text "\n"
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

    def name = "B#{@idx}"

    def << insn
      @instructions << insn
    end

    def edges = @instructions.last.dests

    def successors = edges.map(&:block)

    def out_vregs = @instructions.last.dests.map(&:args).reduce([], :+).grep(VReg)

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

    def dests = ins.grep(Edge)

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

    def inspect = "$#{val.inspect}"
  end

  class VReg      < Operand
    attr_reader :num
    def initialize num
      @num = num
    end

    def inspect = "V#{@num}"

    def as_vreg = self
  end

  class PReg      < Operand
    attr_reader :name

    def initialize name
      raise ArgumentError unless name
      @name = name
    end

    def inspect = "P#{@name}"

    def == other
      other.is_a?(PReg) && @name == other.name
    end
  end

  class StackSlot < Operand
    attr_reader :index

    def initialize index
      @index = index
    end

    def inspect = "Stack[#{@index}]"

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
