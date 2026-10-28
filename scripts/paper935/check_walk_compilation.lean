import ECDSAAdd.Arithmetic.Paper935.AuthorWalkCompiler

open ECDSAAdd.Arithmetic.Paper935

-- Reproducible execution diagnostic, not a theorem or failure-probability sample.
-- Run with: lake env lean scripts/paper935/check_walk_compilation.lean
#eval compileAuthorWalk.map fun slots =>
  let peak := slots.foldl (fun peak Q =>
    max peak (max Q.slot.front.addArena.live.card
      (max Q.slot.front.counterArena.live.card
        (max Q.slot.postArena.live.card Q.detectorArena.live.card)))) walkSeedArena.live.card
  (slots.length,peak,(slots.map (fun Q => Q.history.record.length)).getLastD 0)
