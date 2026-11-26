import OrderedPartitions.ThreePoleData.Block06
import OrderedPartitions.ThreePoleTaylorCell

namespace OrderedPartitions.ThreePoleCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows06_taylor : rows06.all Cell.taylorPass = true := by decide +kernel
end OrderedPartitions.ThreePoleCert
