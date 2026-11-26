import OrderedPartitions.ThreePoleData.Block14
import OrderedPartitions.ThreePoleTaylorCell

namespace OrderedPartitions.ThreePoleCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows14_taylor : rows14.all Cell.taylorPass = true := by decide +kernel
end OrderedPartitions.ThreePoleCert
