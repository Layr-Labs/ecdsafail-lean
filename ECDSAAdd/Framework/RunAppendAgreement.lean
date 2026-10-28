import ECDSAAdd.Framework.WireRename
namespace ECDSAAdd
attribute [local irreducible] run measurementCount

/-- Exact measured composition with prefixes partitioned by actual counts. -/
theorem run_append_agreement (p r q v : Program) (s : State) (m : List Bool)
    (counts : measurementCount r=measurementCount p)
    (first : run p (m.take (measurementCount p)) s=run r (m.take (measurementCount p)) s)
    (second : run q (m.drop (measurementCount p)) (run p (m.take (measurementCount p)) s)=
      run v (m.drop (measurementCount p)) (run p (m.take (measurementCount p)) s)) :
    run (p++q) m s=run (r++v) m s := by
  rw [run_append,run_append,counts,←first]
  exact second
end ECDSAAdd
#print axioms ECDSAAdd.run_append_agreement
