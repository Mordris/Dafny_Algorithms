method partition(A:array<int>, lo:int, hi:int) returns (pivot:int)
  requires 0 <= lo < hi <= A.Length
  ensures 0 <= lo <= pivot < hi <= A.Length
  // The partition method takes an array A, a lower bound lo, and an upper bound hi,
  // and returns the pivot index such that all elements to the left of the pivot
  // are less than or equal to the pivot, and all elements to the right are greater
  // than the pivot.

  requires hi < A.Length ==> forall k :: lo <= k < hi ==> A[k] < A[hi]
  // Requires that if hi is within the array bounds, all elements from lo to hi-1
  // are less than the element at index hi.

  ensures  hi < A.Length ==> forall k :: lo <= k < hi ==> A[k] < A[hi]
  // Ensures that if hi is within the array bounds, all elements from lo to hi-1
  // are less than the element at index hi.

  requires 0 < lo ==> forall k :: lo <= k < hi ==> A[lo-1] <= A[k]
  // Requires that if lo is greater than 0, all elements from lo to hi-1 are greater
  // than or equal to the element at index lo-1.

  ensures  0 < lo ==> forall k :: lo <= k < hi ==> A[lo-1] <= A[k]
  // Ensures that if lo is greater than 0, all elements from lo to hi-1 are greater
  // than or equal to the element at index lo-1.

  ensures forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k]
  // Ensures that all elements outside the partitioned range remain unchanged.

  ensures forall k :: lo <= k < pivot ==> A[k] < A[pivot]
  // Ensures that all elements from lo to pivot-1 are less than the element at pivot.

  ensures forall k :: pivot < k < hi ==> A[pivot] <= A[k]
  // Ensures that all elements from pivot+1 to hi-1 are greater than or equal to
  // the element at pivot.

  modifies A
{
  pivot := lo;
  var i := lo+1;
  while i < hi
    invariant 0 <= lo <= pivot < i <= hi
    // Invariant to ensure valid indices during the loop iterations.

    invariant forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k]
    // Invariant to ensure elements outside the partitioned range remain unchanged.

    invariant forall k :: (lo <= k < pivot) ==> A[k] < A[pivot]
    // Invariant to ensure elements from lo to pivot-1 are less than the pivot element.

    invariant forall k :: (pivot < k < i)   ==> A[pivot] <= A[k]
    // Invariant to ensure elements from pivot+1 to i-1 are greater than or equal to
    // the pivot element.

    invariant hi < A.Length ==> forall k :: lo <= k < hi ==> A[k] < A[hi]
    // Invariant to ensure that if hi is within the array bounds, all elements from lo
    // to hi-1 are less than the element at hi.

    invariant 0  < lo       ==> forall k :: lo <= k < hi ==> A[lo-1] <= A[k]
    // Invariant to ensure that if lo is greater than 0, all elements from lo to hi-1
    // are greater than or equal to the element at lo-1.

  {
    if A[i] < A[pivot] {
      var j := i-1;
      var tmp := A[i];
      A[i] := A[j];
      while pivot < j
        invariant forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k]
        // Invariant to ensure elements outside the partitioned range remain unchanged.

        invariant forall k :: (pivot < k <= i)  ==> A[pivot] <= A[k]
        // Invariant to ensure elements from pivot+1 to i are greater than or equal to
        // the pivot element.

        invariant forall k :: (lo <= k < pivot) ==> A[k] < A[pivot]
        // Invariant to ensure elements from lo to pivot-1 are less than the pivot element.

        invariant A[pivot] > tmp
        // Invariant to ensure the pivot element is greater than the temporary element.

        invariant hi < A.Length ==> forall k :: lo <= k < hi ==> A[k] < A[hi]
        // Invariant to ensure that if hi is within the array bounds, all elements from lo
        // to hi-1 are less than the element at hi.

        invariant 0  < lo       ==> forall k :: lo <= k < hi ==> A[lo-1] <= A[k]
        // Invariant to ensure that if lo is greater than 0, all elements from lo to hi-1
        // are greater than or equal to the element at lo-1.

      {
        A[j+1] := A[j];
        j := j-1;
      }
      A[pivot+1] := A[pivot];
      A[pivot] := tmp;
      pivot := pivot+1;
    }
    i := i+1;
  }
}

predicate sorted(A:array<int>)
  reads A
{
  forall m,n :: 0 <= m < n < A.Length ==> A[m] <= A[n]
  // Predicate to check if an array is sorted in non-decreasing order.
}

predicate sorted_between(A: array<int>, lo: int, hi: int)
  reads A
  requires 0 <= lo <= hi <= A.Length
{
  forall m, n :: lo <= m < n < hi ==> A[m] <= A[n]
  // Predicate to check if an array is sorted between indices lo and hi-1.
}

method quicksort_between(A:array<int>, lo:int, hi:int)
  requires 0 <= lo <= hi <= A.Length
  requires hi < A.Length ==> forall k :: lo <= k < hi ==> A[k] < A[hi]
  ensures  hi < A.Length ==> forall k :: lo <= k < hi ==> A[k] < A[hi]
  requires 0 < lo ==> forall k :: lo <= k < hi ==> A[lo-1] <= A[k]
  ensures  0 < lo ==> forall k :: lo <= k < hi ==> A[lo-1] <= A[k]
  ensures forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k]
  // old(A[k]) evaluates to the value of A[k] on entry to the method, so this
  // checks that only values in A[lo..hi] can be modified by this method

  ensures sorted_between(A, lo, hi)
  // Ensures that the elements between lo and hi-1 are sorted after the method call.

  modifies  A
  decreases hi - lo
{
  if lo+1 >= hi { return; }
  var pivot := partition(A, lo, hi);
  quicksort_between(A, lo, pivot);
  quicksort_between(A, pivot+1, hi);
}

method quicksort(A:array<int>)
  modifies A
  ensures sorted(A)
{
  quicksort_between(A, 0, A.Length);
}

method Main() {
  var A:array<int> := new int[7] [4,0,1,9,7,1,2];
  print "Before: ", A[0], A[1], A[2], A[3], A[4], A[5], A[6], "\n";
  quicksort(A);
  print "After:  ", A[0], A[1], A[2], A[3], A[4], A[5], A[6], "\n";
  assert sorted(A);
}