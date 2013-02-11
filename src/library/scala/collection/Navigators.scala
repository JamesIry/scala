package scala.collection

object Navigators {
/*  def navigator[A,B](coll: immutable.TreeMap[A,B]) = new immutable.TreeMapNavigator(coll)
  def navigator[A](coll: List[A]) = new immutable.ListNavigator(coll)
  def navigator[A](coll: Vector[A]) = new immutable.VectorNavigator(coll)
*/}

/*
final class ListNavigator2[A] private (left: List[A], right: List[A]) extends  LinearNavigator2[A, List[A], ListNavigator2[A]] {
  def prev = left.headOption map {h => (new ListNavigator2[A](left.tail, h :: right), h)}
  def next = right.headOption map {h => (new ListNavigator2[A](h :: left, right.tail), h)}
  def insertNext(element: A) = new ListNavigator2[A](left, element :: right)
  def insertPrev(element: A) = new ListNavigator2[A](element :: left, right)
  
}

*/
//{
/*  def this(coll: List[A]) = this(Nil, coll.headOption, coll drop 1)
  
  override def elementOption = focus
  override def prevDefined = left.nonEmpty
  override def prev = new ListNavigator(left drop 1, left.headOption, elementOption.toList ++ right)
  override def nextDefined = right.nonEmpty
  override def next = new ListNavigator(elementOption.toList ++ left, right.headOption, right drop 1)
  override def insert(element: A) = new ListNavigator(left, Some(element), elementOption.toList ++ right)
  override def replaceWith(element: A) = {throwIfUnfocused; new ListNavigator(left, Some(element), right)}
  override def removeFocused = {throwIfUnfocused; new ListNavigator(left, right.headOption, right drop 1)}
  override def underlying = left.reverse ++ elementOption.toList ++ right
  override def navigatorType = "ListNavigator"
  */
  
  
//}
/*
import colleciton.immutable.TreeMap

final class TreeMapNavigator[A, B] private(tree: RB.Tree[A, B], focus: RB.Tree[A,B], prevUp: Option[TreeMapNavigator[A, B]], nextUp: Option[TreeMapNavigator[A, B]], ordering: Ordering[A])
    extends LinearNavigator[(A, B), TreeMap[A,B], TreeMapNavigator[A, B]] 
    with    Manipulator[(A, B), TreeMap[A,B], TreeMapNavigator[A, B]]
{
  private def this(tree: RB.Tree[A,B], ordering: Ordering[A]) = this(tree, tree, None, None, ordering)
  def this(map: TreeMap[A,B]) = this(map.treeImpl, map.ordering)
  
  def create(focus: RB.Tree[A,B], prevUp: Option[TreeMapNavigator[A, B]], nextUp: Option[TreeMapNavigator[A, B]]) = 
    new TreeMapNavigator(tree, focus, prevUp, nextUp, ordering)
  
  override def elementFocused = nonEmpty(focus)
  override def element = {
    throwIfUnfocused
    (focus.key, focus.value)
  }
  override def prevDefined = leftChildDefined || prevUp.isDefined
  override def prev: TreeMapNavigator[A, B] = 
    if(leftChildDefined) {
      @tailrec def findRightMost(p: TreeMapNavigator[A, B]): TreeMapNavigator[A, B] = if(p.rightChildDefined) findRightMost(p.rightChild) else p
      findRightMost(leftChild)
    } else (prevUp getOrElse leftChild)
    
  override def nextDefined = rightChildDefined || nextUp.isDefined
  override def next: TreeMapNavigator[A, B] =
    if(rightChildDefined) {
      @tailrec def findLeftMost(p: TreeMapNavigator[A, B]): TreeMapNavigator[A, B] = if(p.leftChildDefined) findLeftMost(p.leftChild) else p
      findLeftMost(rightChild)
    } else (nextUp getOrElse rightChild)

  override def insert(element: (A, B)): TreeMapNavigator[A, B] = new TreeMapNavigator(underlying + element) refocus element._1
  override def replaceWith(element: (A,B)): TreeMapNavigator[A, B] = 
    new TreeMapNavigator(underlying - key) insert element    
  override def removeFocused: TreeMapNavigator[A, B] = 
    new TreeMapNavigator(underlying - key) refocus key
  override def underlying = new TreeMap(tree)(ordering)
  override def navigatorType = "TreeMapNavigator"
  
  def key = {throwIfUnfocused; focus.key}
  def value = {throwIfUnfocused; focus.value}
  
  private def nonEmpty(t: RB.Tree[_, _]) = !RB.isEmpty(t)
  private def leftChildDefined = nonEmpty(focus) && nonEmpty(focus.left)
  private def rightChildDefined = nonEmpty(focus) && nonEmpty(focus.right) 
  
  private def leftChild: TreeMapNavigator[A, B] = 
    if (RB.isEmpty(focus)) this 
    else {
      val newFocus = if(leftChildDefined) focus.left else null
      create(newFocus, prevUp, Some(this))
    }
  private def rightChild: TreeMapNavigator[A, B] = 
    if (RB.isEmpty(focus)) this
    else {
      val newFocus = if(rightChildDefined) focus.right else null
      create(newFocus, Some(this), nextUp)
    }
  @tailrec
  private def refocus(newKey: A): TreeMapNavigator[A, B] = {
    val c = if (elementFocused) ordering compare (newKey, key) else 0
    if (c == 0) this
    else if (c > 0) rightChild refocus newKey
    else if (c < 0 && leftChildDefined) leftChild refocus newKey
    else this
  }
} 


final class ListNavigator[A] private[immutable](left: List[A], focus: Option[A], right: List[A]) extends  LinearNavigator[A, List[A], ListNavigator[A]] with Manipulator[A, List[A], ListNavigator[A]] {
  def this(coll: List[A]) = this(Nil, coll.headOption, coll drop 1)
  
  override def elementOption = focus
  override def prevDefined = left.nonEmpty
  override def prev = new ListNavigator(left drop 1, left.headOption, elementOption.toList ++ right)
  override def nextDefined = right.nonEmpty
  override def next = new ListNavigator(elementOption.toList ++ left, right.headOption, right drop 1)
  override def insert(element: A) = new ListNavigator(left, Some(element), elementOption.toList ++ right)
  override def replaceWith(element: A) = {throwIfUnfocused; new ListNavigator(left, Some(element), right)}
  override def removeFocused = {throwIfUnfocused; new ListNavigator(left, right.headOption, right drop 1)}
  override def underlying = left.reverse ++ elementOption.toList ++ right
  override def navigatorType = "ListNavigator"
}

final class VectorNavigator[A](coll: Vector[A], _focus: Int) extends LinearNavigator[A, Vector[A], VectorNavigator[A]] with Manipulator[A, Vector[A], VectorNavigator[A]] {
  def this(coll: Vector[A]) = this(coll, 0)
  import Math.{max, min}
  
  val focus = max(min(_focus, coll.length), -1)

  override def elementFocused = focus >= 0 && focus < coll.length
  override def element = {
    throwIfUnfocused
    coll(focus)
  }
  override def prevDefined = focus > 0
  override def prev = new VectorNavigator(coll, focus - 1)
  override def nextDefined = focus < coll.length - 1
  override def next = new VectorNavigator(coll, focus + 1)
  override def insert(element: A) = {
    val localFocus = max(focus, 0)
    new VectorNavigator(coll.dropRight(coll.length - localFocus) ++ (element +: coll.drop(localFocus)), localFocus)
  }
  override def replaceWith(element: A) = {
    throwIfUnfocused
    new VectorNavigator(coll.updated(focus, element), focus)
  }
  override def removeFocused = {
    throwIfUnfocused
    new VectorNavigator(coll.dropRight(coll.length - focus) ++ coll.drop(focus + 1), focus)
  }
  override def underlying = coll 
  override def navigatorType = "VectorNavigator"
}
*/