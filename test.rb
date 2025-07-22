require "pp"
require "regalloc"
require "minitest/autorun"

def bitset_to_names(bitset, func)
  result = []
  each_bit(bitset) do |idx|
    result << func.vreg(idx)
  end
  result
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

class LivenessTests < Minitest::Test
  attr_reader :func

  def setup
    @func = build_func
  end

  def test_live_in
    live_in = func.analyze_liveness
    assert_equal bitset_to_names(live_in[@b1], func), []
    assert_equal bitset_to_names(live_in[@b2], func), [@r10]
    assert_equal bitset_to_names(live_in[@b3], func), [@r10, @r12, @r13]
    assert_equal bitset_to_names(live_in[@b4], func), [@r10, @r12]
  end

  def test_numbering
    func.analyze_liveness
    func.number_instructions!
    nums = func.instructions.compact.map(&:number)
    assert_equal nums, nums.uniq
  end

  def test_build_intervals
    # for each block b in order do
    #   live = live_in[b]
    #
    #   for each phi function phi of successors of b do
    #     live.add(phi.inputOf(b))
    #
    #   for each opd in live do
    #     intervals[opd].addRange(b.from, b.to)
    #
    #   for each operation op of b in reverse order do
    #     for each output operand opd of op do
    #       intervals[opd].setFrom(op.id)
    #
    #     for each input operand opd of op do
    #       intervals[opd].addRange(b.from, op.id)
    #
    pp func
    live_in = func.analyze_liveness
    func.number_instructions!
    intervals = func.build_intervals live_in
    assert_equal [16..36], intervals[@r10].ranges
    assert_equal [16..20], intervals[@r11].ranges
    assert_equal [20..28, 34..36], intervals[@r12].ranges
    assert_equal [20..30], intervals[@r13].ranges
    assert_equal [28..34], intervals[@r14].ranges
    assert_equal [30..34], intervals[@r15].ranges
  end

  def build_func
    func = Regalloc::Function.new

    r10 = @r10 = func.next_vreg
    r11 = @r11 = func.next_vreg
    r12 = @r12 = func.next_vreg
    r13 = @r13 = func.next_vreg
    r14 = nil
    r15 = nil

    b1 = @b1 = func.new_block
    b2 = @b2 = func.new_block
    b3 = @b3 = func.new_block
    b4 = @b4 = func.new_block

    b1.define(r10, r11) do
      jump(edge(b2, [imm(1), r11]))
    end

    b2.define(r12, r13) do
      cmp(r13, imm(1))
      blt(iftrue: edge(b4), iffalse: edge(b3))
    end

    b3.define do
      r14 = mul(r12, r13)
      r15 = sub(r13, imm(1))
      jump(edge(b2, [r14, r15]))
    end

    @r14 = r14
    @r15 = r15

    b4.define do
      out = add(r10, r12)
      ret out
    end

    func.entry_block = b1
    func
  end
end
