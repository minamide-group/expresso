package machine

import org.scalatest.funsuite._
import com.github.kmn4.expresso.language._

class PreImageTest extends AnyFunSuite {
  test("preimageIter") {
    val alpha = "ab".toSet
    val replaceAll = Transduction.ReplaceAll("aa", "b").toSST(alpha)
    val bstar = RegExp.StarExp(RegExp.CharExp('b')).toNFA(alpha)
    val iter = replaceAll.toParikhSST[Nothing, Nothing].preimageIter(bstar.toDFA.toParikhAutomaton)
    val pas = iter.toSeq
    def accepts(s: String): Boolean = pas.exists(pa => pa.accept(Map.empty)(s.toSeq))
    assert(accepts(""))
    assert(accepts("aa"))
    assert(accepts("aab"))
    assert(accepts("bbaa"))
    assert(!accepts("ab"))
    assert(!accepts("a"))
    assert(!accepts("baba"))
  }
}
