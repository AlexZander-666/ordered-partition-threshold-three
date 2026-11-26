import OrderedPartitions.ThreePoleData.Block16
import OrderedPartitions.ThreePoleTaylorCell

namespace OrderedPartitions.ThreePoleCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows16_taylor : rows16.all Cell.taylorPass = true := by decide +kernel
end OrderedPartitions.ThreePoleCert
