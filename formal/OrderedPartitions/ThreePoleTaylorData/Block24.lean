import OrderedPartitions.ThreePoleData.Block24
import OrderedPartitions.ThreePoleTaylorCell

namespace OrderedPartitions.ThreePoleCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows24_taylor : rows24.all Cell.taylorPass = true := by decide +kernel
end OrderedPartitions.ThreePoleCert
