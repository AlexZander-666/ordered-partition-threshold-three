import OrderedPartitions.ThreePoleData.Block10
import OrderedPartitions.ThreePoleTaylorCell

namespace OrderedPartitions.ThreePoleCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows10_taylor : rows10.all Cell.taylorPass = true := by decide +kernel
end OrderedPartitions.ThreePoleCert
