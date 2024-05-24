// Define the datatype List with generic type T
datatype List<T> = 
  Nil                 // An empty list
  | Cons(head: T, tail: List<T>) // A non-empty list with a head and a tail

// Top-level function to initiate MergeSort
function MergeSort(ls: List<int>): List<int> {
  // Calls the auxiliary function with the list and its length
  MergeSortAux(ls, Length(ls))
}

// Auxiliary function for MergeSort
function MergeSortAux(ls: List<int>, len: nat): List<int>
  requires len == Length(ls) // Precondition: len must be the length of the list
  decreases len // To prove termination: len decreases with each call
{
  if len < 2 then
    // Base case: lists with less than 2 elements are already sorted
    ls
  else
    // Split the list into two halves
    var (left, right) := Split(ls, len / 2);
    // Recursively sort and merge the two halves
    Merge(MergeSortAux(left, len / 2), MergeSortAux(right, len - len / 2))
}

// Function to split a list into two parts
function Split(ls: List<int>, n: nat): (List<int>, List<int>)
  decreases ls // To prove termination: ls gets smaller with each call
  requires n <= Length(ls) // Precondition: n must be less than or equal to the length of the list
  ensures var (left, right) := Split(ls, n);
          Length(left) == n && Length(right) == Length(ls) - n && Append(left, right) == ls // Postcondition: split correctly
{
  if n == 0 then
    // Base case: if n is 0, the left part is empty, and the right part is the original list
    (Nil, ls)
  else
    // Recursively split the tail of the list
    var (l, r) := Split(ls.tail, n - 1);
    // Construct the result with the current head in the left part
    (Cons(ls.head, l), r)
}

// Function to merge two sorted lists into a single sorted list
function Merge(ls1: List<int>, ls2: List<int>): List<int> {
  match (ls1, ls2)
  case (Nil, Nil) => Nil // Both lists are empty
  case (Cons(_, _), Nil) => ls1 // Only the first list is non-empty
  case (Nil, Cons(_, _)) => ls2 // Only the second list is non-empty
  case (Cons(x, xtail), Cons(y, ytail)) =>
    // Both lists are non-empty, compare the heads and merge accordingly
    if x <= y then
      Cons(x, Merge(xtail, ls2)) // x is smaller or equal, so include x first
    else
      Cons(y, Merge(ls1, ytail)) // y is smaller, so include y first
}

// Lemma to ensure MergeSort produces a sorted list
lemma MergeSortOrdered(ls: List<int>)
  ensures Ordered(MergeSort(ls)) // Postcondition: the result is ordered
{
  // Call the auxiliary lemma with the length of the list
  MergeSortAuxOrdered(ls, Length(ls));
}

// Auxiliary lemma to ensure MergeSortAux produces a sorted list
lemma MergeSortAuxOrdered(ls: List<int>, len: nat)
  requires len == Length(ls) // Precondition: len must be the length of the list
  ensures Ordered(MergeSortAux(ls, len)) // Postcondition: the result is ordered
  decreases len // To prove termination: len decreases with each call
{
  if 2 <= len {
    // If the list length is at least 2, split it and recursively check ordering
    var (left, right) := Split(ls, len / 2);
    // Ensure the merged result is ordered
    MergeOrdered(MergeSortAux(left, len / 2), MergeSortAux(right, len - len / 2));
  }
}

// Lemma to ensure merging two ordered lists results in an ordered list
lemma MergeOrdered(ls1: List<int>, ls2: List<int>)
  requires Ordered(ls1) && Ordered(ls2) // Precondition: both lists must be ordered
  ensures Ordered(Merge(ls1, ls2)) // Postcondition: the merged result is ordered
{}

// Function to compute the length of a list
function Length(ls: List<int>): nat {
  match ls
  case Nil => 0 // An empty list has length 0
  case Cons(_, tail) => 1 + Length(tail) // A non-empty list has length 1 + the length of the tail
}

// Function to append two lists
function Append(ls1: List<int>, ls2: List<int>): List<int> {
  match ls1
  case Nil => ls2 // An empty list appended to another list is just the other list
  case Cons(x, tail) => Cons(x, Append(tail, ls2)) // Recursively append the tail to the second list
}

// Predicate to check if a list is ordered
predicate Ordered(ls: List<int>) {
  match ls
  case Nil => true // An empty list is ordered
  case Cons(_, Nil) => true // A single-element list is ordered
  case Cons(x, Cons(y, _)) => x <= y && Ordered(ls.tail) // A list is ordered if the head is <= the next element and the tail is ordered
}

// Test method to verify that MergeSortOrdered works
method TestMergeSortOrdered(){
  var ls := Cons(1, Cons(2, Cons(3, Nil))); // Create a test list
  assert Ordered(ls); // Assert that the test list is ordered
  MergeSortOrdered(ls); // Verify that MergeSort maintains the ordering
}
