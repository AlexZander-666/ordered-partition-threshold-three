import OrderedPartitions.ThreePoleData.Block21
import OrderedPartitions.ThreePoleTaylorCell

namespace OrderedPartitions.ThreePoleCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows21_taylor : rows21.all Cell.taylorPass = true := by decide +kernel
end OrderedPartitions.ThreePoleCert
