import OrderedPartitions.ThreePoleData.Block00
import OrderedPartitions.ThreePoleData.Block01
import OrderedPartitions.ThreePoleData.Block02
import OrderedPartitions.ThreePoleData.Block03
import OrderedPartitions.ThreePoleData.Block04
import OrderedPartitions.ThreePoleData.Block05
import OrderedPartitions.ThreePoleData.Block06
import OrderedPartitions.ThreePoleData.Block07
import OrderedPartitions.ThreePoleData.Block08
import OrderedPartitions.ThreePoleData.Block09
import OrderedPartitions.ThreePoleData.Block10
import OrderedPartitions.ThreePoleData.Block11
import OrderedPartitions.ThreePoleData.Block12
import OrderedPartitions.ThreePoleData.Block13
import OrderedPartitions.ThreePoleData.Block14
import OrderedPartitions.ThreePoleData.Block15
import OrderedPartitions.ThreePoleData.Block16
import OrderedPartitions.ThreePoleData.Block17
import OrderedPartitions.ThreePoleData.Block18
import OrderedPartitions.ThreePoleData.Block19
import OrderedPartitions.ThreePoleData.Block20
import OrderedPartitions.ThreePoleData.Block21
import OrderedPartitions.ThreePoleData.Block22
import OrderedPartitions.ThreePoleData.Block23
import OrderedPartitions.ThreePoleData.Block24
import OrderedPartitions.ThreePoleData.Block25
import OrderedPartitions.ThreePoleData.Block26

namespace OrderedPartitions.ThreePoleCert

def cells : List Cell := rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26

private theorem join (a b : List Cell) (x : a.all Cell.passes = true) (y : b.all Cell.passes = true) : (a++b).all Cell.passes = true := by rw [List.all_append,x,y]; rfl

set_option maxHeartbeats 0 in
theorem all_pass : cells.all Cell.passes = true :=
  join rows00 (rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows00_pass (join rows01 (rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows01_pass (join rows02 (rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows02_pass (join rows03 (rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows03_pass (join rows04 (rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows04_pass (join rows05 (rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows05_pass (join rows06 (rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows06_pass (join rows07 (rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows07_pass (join rows08 (rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows08_pass (join rows09 (rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows09_pass (join rows10 (rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows10_pass (join rows11 (rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows11_pass (join rows12 (rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows12_pass (join rows13 (rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows13_pass (join rows14 (rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows14_pass (join rows15 (rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows15_pass (join rows16 (rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows16_pass (join rows17 (rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows17_pass (join rows18 (rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows18_pass (join rows19 (rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows19_pass (join rows20 (rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows20_pass (join rows21 (rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows21_pass (join rows22 (rows23 ++ rows24 ++ rows25 ++ rows26) rows22_pass (join rows23 (rows24 ++ rows25 ++ rows26) rows23_pass (join rows24 (rows25 ++ rows26) rows24_pass (join rows25 (rows26) rows25_pass (rows26_pass))))))))))))))))))))))))))

#print axioms all_pass
end OrderedPartitions.ThreePoleCert
