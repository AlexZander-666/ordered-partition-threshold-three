import OrderedPartitions.ThreePoleData.Block02
import OrderedPartitions.ThreePoleTaylorCell

namespace OrderedPartitions.ThreePoleCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows02_taylor : rows02.all Cell.taylorPass = true := by decide +kernel
end OrderedPartitions.ThreePoleCert
