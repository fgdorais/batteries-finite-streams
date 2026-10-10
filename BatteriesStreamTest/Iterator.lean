import BatteriesStream.Iterator

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
