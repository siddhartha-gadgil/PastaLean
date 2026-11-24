import PastaLean.PyVerify.Twin

open PastaLean

/-! A table row whose bridge lemma is not available is not an error: `twin_table` leaves one goal per
instantiation used, in the shape of the bridge lemma. (Its own module: it removes lemmas from the
`@[twin]` set.) -/

attribute [-twin] PastaLean.Twin.pyArrayPopValue_twin PastaLean.Twin.pyArrayAppend_twin

namespace PastaLean.TwinTest

def heads (xs : List Int) (ss : List String) : Int × String × List Int :=
  (pyPopValue xs (-1), pyPopValue ss (-1), pyAppend xs 5)
def heads'rn (xs : Array Int) (ss : Array String) : Int × String × Array Int :=
  (pyArrayPopValue xs (-1), pyArrayPopValue ss (-1), pyArrayAppend xs 5)

theorem heads_twin : twin% heads := by
  twin_table
  case prim.pyArrayPopValue_1 | prim.pyArrayPopValue_2 =>
    intro l i; exact Twin.pyArrayPopValue_twin l i
  case prim.pyArrayAppend => intro l v; exact Twin.pyArrayAppend_twin l v

end PastaLean.TwinTest
