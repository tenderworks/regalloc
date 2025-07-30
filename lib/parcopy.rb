require 'minitest'
require 'minitest/autorun'

# Resources:
# https://bboissin.appspot.com/static/upload/bboissin-thesis-2010-09-22.pdf (p80)
# github.com/pfalcon/parcopy

def sequentialize copies
  ready = []  # Contains only destination regs ("available")
  to_do = []  # Contains only destination regs
  pred = {}  # Map of destination reg -> what reg is written to it (its source)
  loc = {}  # Map of reg -> the current location where the initial value of reg is available ("resource")
  result = []

  emit_copy = -> (src, dst) {
    result << [src, "->", dst]
  }

  # loc[x] is nil if x not in loc
  # copies.each do |(src, dst)|
  #   loc[dst] = nil
  # end

  copies.each do |(src, dst)|
    loc[src] = src
    if pred.key? dst  # Alternatively, to_do.include? dst
      raise "Conflicting assignments to destination #{dst}, latest: #{[dst, src]}"
    end
    pred[dst] = src
    to_do << dst
  end

  copies.each do |(src, dst)|
    if !loc[dst]
      # All destinations that are not also sources can be written to immediately (tree leaves)
      ready << dst
    end
  end

  while !to_do.empty?
    while b = ready.pop
      # next if !pred.include?(b)
      a = loc[pred[b]] # a in the paper
      emit_copy.(a, b)
      # pred[b] is now living at b
      loc[pred[b]] = b
      if to_do.include?(a)
        to_do.delete a
      end
      if pred[b] == a && pred.include?(a) #pred.include?(pred[b])
        ready << a
      end
    end

    if to_do.empty?
      break
    end

    dst = to_do.pop
    if dst != loc[pred[dst]]
      emit_copy.(dst, "tmp")
      loc[dst] = "tmp"
      ready << dst
    end
  end
  result
end

class SequentializeTests < Minitest::Test
  def test_empty
    assert_equal [], sequentialize([])
  end

  def test_simple
    #assert_equal [[:a, "->", :b]], sequentialize([[:a, :b]])
    assert_equal [[:b, "->", :c], [:a, "->", :b]], sequentialize([[:a, :b], [:b, :c]])
  end

  def test_multiple
    assert_equal [[:c, "->", :d], [:a, "->", :b]], sequentialize([[:a, :b], [:c, :d]])
  end

  def test_transitive
    assert_equal [[:b, "->", :c], [:a, "->", :b]], sequentialize([[:b, :c], [:a, :b]])
  end

  def test_fan_out
    assert_equal [[:a, "->", :c], [:c, "->", :b]], sequentialize([[:a, :b], [:a, :c]])
  end

  def test_self_loop
    assert_equal [], sequentialize([[:a, :a]])
    assert_equal [], sequentialize([[:a, :a], [:b, :b]])
  end

  def test_loop
    assert_equal [[:a, "->", "tmp"], [:b, "->", :a], ["tmp", "->", :b]], sequentialize([[:a, :b], [:b, :a]])
  end

  def test_duplicate_dst
    assert_raises { sequentialize([:a, :b], [:c, :b]) }
  end

  def test_boissinot_thesis
    assert_equal [[:c, "->", :d], [:b, "->", :c], [:a, "->", :b], [:d, "->", :a]], sequentialize([[:a, :b], [:b, :c], [:c, :a], [:c, :d]])
  end
end
