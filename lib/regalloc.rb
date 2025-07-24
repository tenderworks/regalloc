require "set"

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
      raise if !@range
      @range = Range.new(from, @range.end)
    end
  end

  class Function
    attr_accessor :entry_block
    attr_reader :instructions

    def initialize
      @next_vreg_name = 10
      @next_blk_name = 1
      @vregs = {}
      @instructions = []
    end

    def number_instructions!
      number = 16
      rpo.each do |blk|
        blk.number = number
        @instructions[number] = blk
        number += 2
        blk.instructions.each do |insn|
          @instructions[number] = insn
          insn.number = number
          number += 2
        end
        blk.to = number
      end
    end

    def build_intervals live_in
      intervals = Hash.new { |hash, key| hash[key] = Interval.new }
      rpo.each do |block|
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

    # def allocate_registers
    #   1. schedule (number instructions)
    #   2. backward iteration to calculate live ranges
    #   3. normal linear scan
    #   4. ssa resolution (incl parallel moves)
    # end

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

    def compute_initial_liveness_sets order
      gen = Hash.new 0
      kill = Hash.new 0
      order.each do |block|
        block.instructions.each do |insn|
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

    def successors
      @instructions.last.dests.map(&:block)
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
  end

  class Insn
    attr_reader :name, :out, :ins
    attr_accessor :id, :number

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
      @name.to_s
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
    attr_reader :block, :args

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
