import BatteriesFiniteStreams.Iterator

#guard (Std.Stream.iter [1, 2, 3]).toList == [1, 2, 3]
#guard ((Std.Stream.iter [1, 2, 3]).map (· * 2)).toArray == #[2, 4, 6]

-- Finite iterators are well-founded streams
#guard Std.Stream.toList (Std.toStream (0...3)) == [0, 1, 2]

def sumFor (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in Std.Stream.iter l do
    s := s + x
  return s

#guard sumFor [1, 2, 3] == 6

-- Round trip
#guard Std.Stream.toList (Std.Stream.iter [1, 2, 3]) == [1, 2, 3]
#guard Std.Stream.toList (Std.Stream.iter (Std.Stream.iter "abc".toRawSubstring)) == ['a', 'b', 'c']
#guard (Std.Stream.iter [1, 2, 3]).atIdx? 1 == some 2
#guard (Std.Stream.iter [1, 2, 3]).atIdx? 3 == none
