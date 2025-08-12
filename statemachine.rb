require "pp"
require "regalloc"

def build_mini
  func = Regalloc::Function::new
  func.next_vreg_name = 0
  func.insn_start_number = 0
  b1 = func.new_block
  b1.define do
    v0 = loadi imm(1)
    v1 = loadi imm(2)
    v2 = add v0, v1
    ret v2
  end
  func.entry_block = b1
  func
end

func = build_mini
live_in = func.analyze_liveness
func.number_instructions!
intervals = func.build_intervals live_in
func.ye_olde_linear_scan intervals, 2
