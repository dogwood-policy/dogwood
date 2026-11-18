import Dogwood.Spec
import Dogwood.Eval.Decision
import Dogwood.Thm
import Dogwood.Examples
import Dogwood.Frontend
import Dogwood.Thm.Frontend

/-!
# A formal specification of Dogwood

The specification (`Dogwood.Spec`), an executable evaluator proved to decide it
(`Dogwood.Eval`), its meta-theory (`Dogwood.Thm`), worked examples checked
against the reference interpreter's verdicts (`Dogwood.Examples`), and a port of
the crate's frontend, tested stage by stage against the crate
(`Dogwood.Frontend`). See `README.md`.
-/
