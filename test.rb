require "pp"
require "regalloc"
require "minitest/autorun"

FUNC = Regalloc::Function.new

R10 = FUNC.next_vreg
R11 = FUNC.next_vreg
R12 = FUNC.next_vreg
R13 = FUNC.next_vreg

B1 = FUNC.new_block
B2 = FUNC.new_block
B3 = FUNC.new_block
B4 = FUNC.new_block

B1.define(R10, R11) do
  jump(edge(B2, [imm(1), R11]))
end

B2.define(R12, R13) do
  cmp(R13, imm(1))
  blt(iftrue: edge(B4), iffalse: edge(B3))
end

B3.define do
  r14 = mul(R12, R13)
  r15 = sub(R13, imm(1))
  jump(edge(B2, [r14, r15]))
end

B4.define do
  out = add(R10, R12)
  ret out
end

FUNC.entry_block = B1

def bitset_to_names(bitset)
  result = []
  each_bit(bitset) do |idx|
    result << FUNC.vreg(idx)
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

pp FUNC

class LivenessTests < Minitest::Test
  def test_live_in
    live_in = FUNC.analyze_liveness
    assert_equal bitset_to_names(live_in[B1]), []
    assert_equal bitset_to_names(live_in[B2]), [R10]
    assert_equal bitset_to_names(live_in[B3]), [R10, R12, R13]
    assert_equal bitset_to_names(live_in[B4]), [R10, R12]
  end
end
