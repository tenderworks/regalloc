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

    def edge block, params = []
      Edge.new(block, params)
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

  class Function
    attr_accessor :entry_block

    def initialize
      @next_vreg_name = 0
      @next_blk_name = 1
      @vregs = {}
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

    def analyze_liveness
      # Map from Block to bitset of VRegs live at entry
      order = po
      live_in = Hash.new 0
      changed = true
      while changed
        changed = false
        for block in order
          block_live = block.successors.map { |succ| live_in[succ] }.reduce(0, :|)
          for insn in block.instructions.reverse
            # Defined vregs are not live-in
            out = insn.out&.as_vreg
            if out
              block_live &= ~(1 << out.num)
            end
            # Used vregs are live-in
            block_live |= insn.vreg_ins.map { |vreg| 1 << vreg.num }.reduce(0, :|)
          end
          # Except for block parameters, which are implicitly defined at the
          # start of the block
          for param in block.parameters
            block_live &= ~(1 << param.num)
          end
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

    def po_traversal visited, post_order
      return post_order if visited.include?(self)

      visited.add(self)

      successors.each do |successor|
        successor.po_traversal(visited, post_order)
      end

      post_order << self
      post_order
    end

    def pretty_print(pp)
      pp.text "Block"
      if parameters.any?
        pp.text " (#{parameters.map(&:inspect).join(", ")})"
      end
      pp.text ":"
      pp.breakable
      pp.group(2, "", "") do
        instructions.each do |insn|
          pp.pp insn
          pp.breakable
        end
      end
    end
  end

  class Insn
    attr_reader :name, :out, :ins
    attr_accessor :id

    def initialize name, out, ins
      @name = name
      @out = out
      @ins = ins
    end

    def pretty_print(pp)
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
          result.concat(op.params.grep(VReg))
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
    attr_reader :block, :params

    def initialize block, params
      @block = block
      @params = params
    end

    def inspect
      block_name = @block.name
      if @params.empty?
        "→#{block_name}"
      else
        "→#{block_name}(#{@params.map(&:inspect).join(", ")})"
      end
    end
  end
end

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
