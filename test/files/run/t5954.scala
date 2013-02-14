import scala.tools.partest._

object Test extends DirectTest {
  def code = ???

  def problemCode = """
    package object A {
      class B
      object B
      case class C()
    }
  """

  def driverCode = """
    object Test extends App {
      println(A.C())
    }
  """

  def compileCode(code: String) = {
    val classpath = List(sys.props("partest.lib"), testOutput.path) mkString sys.props("path.separator")
    compileString(newCompiler("-cp", classpath, "-d", testOutput.path))(code)
  }

  def show() : Unit = {
    for (i <- 0 until 2) {
      compileCode(problemCode)
      compileCode(driverCode)
      println(s"success ${i + 1}")
    }
  }
}
