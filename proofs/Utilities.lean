import Lean

open Lean Meta Elab Tactic

/--
Generates a name based on an index (0 -> a, 1 -> b, etc.)
-/
def getAutoName (i : Nat) : Name :=
    s!"var_{i}" |>.toName

syntax (name := renameAutoN) "rename_auto_n " num : tactic

@[tactic renameAutoN]
def evalRenameAutoN : Tactic := fun stx => do
  -- Parse the number 'n' from the tactic call
  let n := stx[1].isNatLit?.getD 0

  liftMetaTactic fun mvarId => do
    let lctx ← getLCtx
    let mut mvarId := mvarId
    let mut foundCount := 0

    for ldecl in lctx do
      if foundCount >= n then break

      -- Check if the hypothesis is inaccessible (has macro scopes or is a dagger/internal name)
      if ldecl.userName.hasMacroScopes || ldecl.userName.toString.startsWith "✝" then
        let newName := getAutoName foundCount
        mvarId ← mvarId.rename ldecl.fvarId newName
        foundCount := foundCount + 1

    return [mvarId]
