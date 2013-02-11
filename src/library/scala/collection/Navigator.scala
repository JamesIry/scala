package scala.collection

import language.higherKinds

/** 
 * A collection that can produce a Navigator
 */
trait LinearNavigable2[A, Coll, Produced <: LinearNavigator2[A, Coll, Produced]] {
  def navigator: Produced
}

/**
 * 
 */
trait LinearNavigator2[A, Coll, Self <: LinearNavigator2[A, Coll, Self]] {
  protected def throwIfNoNext = if (!nextDefined) throwNoNext
  protected def throwNoNext = throw new NoSuchElementException("Attempt to move 'next' past the end of a navigator.")
  def nextDefined: Boolean = nextOption.isDefined
  def nextOption: Option[(Self, A)] = if (nextDefined) Some(next) else None
  def next: (Self, A) = nextOption getOrElse throwNoNext
  def nextElement: A = next._2
  def nextNav: Self = next._1
  def insertNext(element: A): Self
  def removeNext: Self
  def replaceNext(element: A): Self = removeNext insertNext element
  
  protected def throwIfNoPrev = if (!prevDefined) throwNoPrev
  protected def throwNoPrev = throw new NoSuchElementException("Attempt to move 'prev' past the beginning of a navigator.")
  def prevDefined: Boolean = prevOption.isDefined
  def prevOption: Option[(Self, A)] = if (prevDefined) Some(prev) else None
  def prev: (Self, A) = prevOption getOrElse throwNoPrev
  def prevElement: A = prev._2
  def prevNav: Self = prev._1
  def insertPrev(element: A): Self = (prevNav insertNext element).nextNav
  def removePrev: Self = prevNav.removeNext
  def replacePrev(element: A): Self = removePrev insertPrev element
  def toUnderlying : Coll
}

/**
 *  A Navigator is a structure-sharing, immutable, navigable view over a collection. It always
 *  focuses on one element of the underlying collection (unless the collection is empty) and
 *  allows traversal. Different Navigators will facilitate different forms of Navigation
 */
trait Navigator[A, Coll] {
  protected def throwIfUnfocused = if (!elementFocused) throwUnfocused
  protected def throwUnfocused = throw new NoSuchElementException("The navigator is not focused on an element.")
  
  /** True if the Navigator is focused on an element. False only for a Navigator over an empty collection
   *  O(1)
   */
  def elementFocused: Boolean = elementOption.isDefined
  /** The element currently focused by this Navigator. Throws NoSuchElementException if there
   * is no element under focus, e.g. the collection is empty or the navigator has
   * gone past the end
   *  O(1)
   */
  def element: A = elementOption getOrElse throwUnfocused
  /** The element currently focused by this Navigator as an Option. None only if there
   * is no element under focus, e.g. the collection is empty or the navigator has
   * gone past the end
   *  O(1)
   */
  def elementOption: Option[A] = if(elementFocused) Some(element) else None
  /** Returns the collection underlying this Navigator
   *  Big-O complexity depends on the underlying collection
   */
  def underlying: Coll
}

/**
 * A Manipulator is a Navigator with the ability to add and remove elements 
 */
trait Manipulator[A, Coll, Self <: Manipulator[A, Coll, Self]] extends Navigator[A, Coll] {
  /** Inserts an element into the collection and sets the Navigators focus on that element.
   *  Where the new element resides in relation to other elements depends on the underlying
   *  collection.
   *  Big-O complexity will vary depending on the underlying collection.
   */
  def insert(element: A): Self
  /** Replaces the element at the current focus of the Navigator.
   *  nav.remove(x) is functionally equivalent to nav.remove.insert(x), 
   *  however the underlying collection may make replacement less expensive and
   *  on collections with arbitrary ordering such as a hash set the relative
   *  ordering of elements before and after the new one may or may not differ
   *  between nav.replace(x) and nav.remove.insert(x).
   *  Throws NoSuchElementException if there is no element under 
   *  focus, e.g. the collection is empty or the navigator has
   *  Big-O complexity will vary depending on the underlying collection.
   */
  def replaceWith(element: A): Self = removeFocused.insert(element)
  /** Removes the element currently at the focus of this Navigator.
   *  After removal, the element under focus is the "next" element or,
   *  The relative ordering of other elements in the zipper may change
   *  if the underlying collection has an arbitrary ordering, e.g. a hash set.
   *  Throws NoSuchElementException if there is no element under 
   *  focus, e.g. the collection is empty or the navigator has
   *  gone past the end
   *  Big-O complexity depends on the underlying collection
   */
  def removeFocused: Self
}

/**
 *  A LinearNavigator is a Navigator that can traverse forward and backward one element at a time.
 */
trait LinearNavigator[A, Coll, Self <: LinearNavigator[A, Coll, Self]] extends Navigator[A, Coll] {
  /** True if the result of prev.elementDefined would be true
   *  O(log Size) or better, O(1) on most data structures
   */
  def prevDefined: Boolean
  /** The Navigator focused on the "previous" element, if there is one. Otherwise
   * the Navigator with no focus and whose "next" method moves back to this location.
   * In other words, prev may create a Navigator focused just before the first
   * element of the underlying collection while successive uses of prev will
   * not move the Navigator any further. This and the symmetrical behavior
   * of next allows inserting at either end of a LinearNavigator that
   * is also a Manipulator.
   *  O(log Size) or better, O(1) on most data structures
   */
  def prev: Self
  /** True if the result of next.elementDefined would be true
   *  O(log Size) or better, O(1) on most data structures
   */
  def nextDefined: Boolean
  /** The Navigator focused on the "next" element, if there is one. Otherwise
   * the Navigator with no focus and whose "prev" method moves back to this location
   * In other words, next may create a Navigator focused just after the last
   * element of the underlying collection while successive uses of next will
   * not move the Navigator any further. This and the symmetrical behavior
   * of prev allows inserting at either end of a LinearNavigator that
   * is also a Manipulator.
   *  O(log Size) or better, O(1) on most data structures
   */
  def next: Self
  
  def navigatorType: String
  
  override def toString = {
    val prevPrevPrevS = if(prev.prev.prevDefined) "..., " else ""
    val prevPrevS = if(prev.prevDefined) s"${prev.prev.element}, " else ""
    val prevS = if(prevDefined) s"${prev.element}, " else ""
    val currentS = s"[${if(elementFocused) element else ""}]"
    val nextS = if(nextDefined) s", ${next.element}" else ""
    val nextNextS = if(next.nextDefined) s", ${next.next.element}" else ""
    val nextNextNextS = if(next.next.nextDefined) ", ..." else ""
    s"$navigatorType($prevPrevPrevS$prevPrevS$prevS$currentS$nextS$nextNextS$nextNextNextS)"
  }
}



