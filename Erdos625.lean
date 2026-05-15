-- Root module for the Erdos625 library.
-- Loads the Lean-certified companion results, including the fixed-epsilon
-- in-probability theorem `erdos_625_full_clean`, and the analytical wrapper
-- `Erdos625.AnalyticalWrapper`.
--
-- The analytical wrapper is a dependency-closure interface for the full
-- analytical route, not a Lean-certified proof of that route yet: it still
-- exposes the three bridge-input-shaped WHP obligations tracked by the
-- completion gate.
import Erdos625.PublishableProof
import Erdos625.AnalyticalWrapper
import Erdos625.LowBranchCertificate
import Erdos625.LowBranchIntervalSkeleton
import Erdos625.MiddleBranchCertificate
import Erdos625.MiddleBranchIntervalSkeleton
import Erdos625.UpperR2Certificate
import Erdos625.UpperR2IntervalSkeleton
import Erdos625.UpperR2IntervalOutput
