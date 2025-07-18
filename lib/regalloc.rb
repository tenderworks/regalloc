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
    end

    def rpo
      entry_block.po_traversal(Set.new, []).reverse
    end

    def next_vreg
      vreg = VReg.new @next_vreg_name
      @next_vreg_name += 1
      vreg
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

    def succ1
      successors[0]
    end

    def succ2
      successors[1]
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

    def in1; @ins[0]; end
    def in2; @ins[1]; end

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
  end

  class Operand
    def pretty_print(pp)
      pp.text inspect
    end
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
      block_name = @block.name || "Block"
      if @params.any?
        "→#{block_name}(#{@params.map(&:inspect).join(", ")})"
      else
        "→#{block_name}"
      end
    end
  end
end
