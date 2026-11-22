import Ct.Model

/-!
# The leakage model, build-specific part: the default build

The default build's translation names no primitive beyond those of `Ct/Model.lean`. This file
exists because the `hw-sha2` build has one of its own (`lean-hw/Ct/ModelBuild.lean`, the
instrumented intrinsic wrappers); the files that do not depend on the build import it under the
same name in both packages.
-/

namespace Ct.Build

/-- The instrumented primitives of this build beyond those of `Ct/Model.lean`: none. -/
def modelConsts : List Lean.Name := []

end Ct.Build
