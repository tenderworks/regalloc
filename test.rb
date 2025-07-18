require "pp"
require "regalloc"

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

pp FUNC
