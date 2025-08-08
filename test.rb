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

  def test_range
    func = Regalloc::Function.new
    func.next_vreg_name = 0
    func.insn_start_number = 0

    b1 = func.new_block

    # 0: block
    # 2: v0 = $1
    # 4: v1 = add v0, $2
    # 6: ret v1
    #
    # v0: [2, 4)
    # v1: [4, 6)
    v0 = v1 = nil
    b1.define do
      v0 = loadi(imm(5))
      v1 = add(v0, imm(1))
      ret v1
    end

    func.entry_block = b1
    live_in = func.analyze_liveness
    func.number_instructions!
    intervals = func.build_intervals live_in
    assignments, num_stack_slots = func.ye_olde_linear_scan intervals, 1

    func.resolve_ssa intervals, assignments

    assert_equal Regalloc::PReg.new(0), assignments[intervals[v0]]
    assert_equal Regalloc::PReg.new(0), assignments[intervals[v1]]
  end

  def test_live_in
    live_in = func.analyze_liveness
    assert_equal bitset_to_names(live_in[@b1], func), []
    assert_equal bitset_to_names(live_in[@b2], func), [@r10]
    assert_equal bitset_to_names(live_in[@b3], func), [@r10, @r12, @r13]
    assert_equal bitset_to_names(live_in[@b4], func), [@r10, @r12]
  end

  def test_numbering
    func.number_instructions!
    nums = func.instructions.compact.map(&:number)
    assert_equal nums, nums.uniq
  end

  def test_build_live_intervals
    live_in = func.analyze_liveness
    func.number_instructions!
    intervals = func.build_intervals live_in
    assert_equal 16..36, intervals[@r10].range
    assert_equal 16..20, intervals[@r11].range
    assert_equal 20..36, intervals[@r12].range
    assert_equal 20..30, intervals[@r13].range
    assert_equal 28..34, intervals[@r14].range
    assert_equal 30..34, intervals[@r15].range
  end

  def test_linear_scan_no_spill
    live_in = func.analyze_liveness
    func.number_instructions!
    intervals = func.build_intervals live_in
    assignments, num_stack_slots = func.ye_olde_linear_scan intervals, 5
    assert_equal 0, num_stack_slots
    assert_equal Regalloc::PReg.new(0), assignments[intervals[@r10]]
    assert_equal Regalloc::PReg.new(1), assignments[intervals[@r11]]
    assert_equal Regalloc::PReg.new(1), assignments[intervals[@r12]]
    assert_equal Regalloc::PReg.new(2), assignments[intervals[@r13]]
    assert_equal Regalloc::PReg.new(3), assignments[intervals[@r14]]
    assert_equal Regalloc::PReg.new(2), assignments[intervals[@r15]]
  end

  def test_linear_scan_spill
    live_in = func.analyze_liveness
    func.number_instructions!
    intervals = func.build_intervals live_in
    assignments, num_stack_slots = func.ye_olde_linear_scan intervals, 1
    assert_equal 3, num_stack_slots
    assert_equal Regalloc::StackSlot.new(0), assignments[intervals[@r10]]
    assert_equal Regalloc::PReg.new(0), assignments[intervals[@r11]]
    assert_equal Regalloc::StackSlot.new(1), assignments[intervals[@r12]]
    assert_equal Regalloc::PReg.new(0), assignments[intervals[@r13]]
    assert_equal Regalloc::StackSlot.new(2), assignments[intervals[@r14]]
    assert_equal Regalloc::PReg.new(0), assignments[intervals[@r15]]
  end

  def test_linear_scan_spill_less
    live_in = func.analyze_liveness
    func.number_instructions!
    intervals = func.build_intervals live_in
    assignments, num_stack_slots = func.ye_olde_linear_scan intervals, 3
    assert_equal 1, num_stack_slots
    assert_equal Regalloc::StackSlot.new(0), assignments[intervals[@r10]]
    assert_equal Regalloc::PReg.new(1), assignments[intervals[@r11]]
    assert_equal Regalloc::PReg.new(1), assignments[intervals[@r12]]
    assert_equal Regalloc::PReg.new(2), assignments[intervals[@r13]]
    assert_equal Regalloc::PReg.new(0), assignments[intervals[@r14]]
    assert_equal Regalloc::PReg.new(2), assignments[intervals[@r15]]
  end

  def test_resolve
    # func = build_smaller_func
    func = @func
    live_in = func.analyze_liveness
    func.number_instructions!
    intervals = func.build_intervals live_in
    assignments, num_stack_slots = func.ye_olde_linear_scan intervals, 3
    puts "BEFORE"
    pp func
    func.resolve_ssa intervals, assignments
    puts "AFTER"
    pp func
  end

  def test_resolve_critical_edge
    func = build_critical_edge
    live_in = func.analyze_liveness
    func.number_instructions!
    intervals = func.build_intervals live_in
    assignments, num_stack_slots = func.ye_olde_linear_scan intervals, 3
    puts "BEFORE"
    pp func
    func.resolve_ssa intervals, assignments
    puts "AFTER"
    pp func
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

  def build_smaller_func
    ##
    # def foo x
    #   entry(x):
    #   if x < 0 # blt iftrue: lt_side(x), iffalse: gt_side(x)

    #     lt_side(y):
    #     foo = rand()
    #     cmp foo, 0.5
    #     blt rand_lt_side(y), rand_gt_side(y)
    #     if rand() < 0.5
    #       # rand_lt_side(z):
    #     end
    #   else # gt_side(y):
    #   end
    # end
    func = Regalloc::Function.new

    r10 = @r10 = func.next_vreg
    r11 = @r11 = func.next_vreg
    r12 = @r12 = func.next_vreg
    r13 = @r13 = func.next_vreg

    b1 = @b1 = func.new_block
    b2 = @b2 = func.new_block
    b3 = @b3 = func.new_block

    b1.define(r10, r11) do
      cmp r10, imm(0)
      blt iftrue: edge(b2, [r11]), iffalse: edge(b3, [imm(1)])
    end

    b2.define(r13) do
      out = add(r13, imm(1))
      ret out
    end

    b3.define(r12) do
      out = sub(r12, imm(1))
      ret out
    end

    func.entry_block = b1
    func
  end

  def build_critical_edge
    func = Regalloc::Function::new
    b1 = func.new_block
    b2 = func.new_block
    b3 = func.new_block
    b1.define do
      i1 = loadi imm(123)
      i2 = loadi imm(456)
      blt iftrue: edge(b2, []), iffalse: edge(b3, [i1])
    end
    b2.define do
      i3 = loadi imm(789)
      i4 = add i3, imm(1)
      jump edge(b3, [i4])
    end
    i7 = func.next_vreg
    b3.define(i7) do
      i8 = mul i7, imm(2)
      ret i8
    end
    func.entry_block = b1
    func
  end
end
