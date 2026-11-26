import OrderedPartitions.ThreePoleTaylorData.Block00
import OrderedPartitions.ThreePoleTaylorData.Block01
import OrderedPartitions.ThreePoleTaylorData.Block02
import OrderedPartitions.ThreePoleTaylorData.Block03
import OrderedPartitions.ThreePoleTaylorData.Block04
import OrderedPartitions.ThreePoleTaylorData.Block05
import OrderedPartitions.ThreePoleTaylorData.Block06
import OrderedPartitions.ThreePoleTaylorData.Block07
import OrderedPartitions.ThreePoleTaylorData.Block08
import OrderedPartitions.ThreePoleTaylorData.Block09
import OrderedPartitions.ThreePoleTaylorData.Block10
import OrderedPartitions.ThreePoleTaylorData.Block11
import OrderedPartitions.ThreePoleTaylorData.Block12
import OrderedPartitions.ThreePoleTaylorData.Block13
import OrderedPartitions.ThreePoleTaylorData.Block14
import OrderedPartitions.ThreePoleTaylorData.Block15
import OrderedPartitions.ThreePoleTaylorData.Block16
import OrderedPartitions.ThreePoleTaylorData.Block17
import OrderedPartitions.ThreePoleTaylorData.Block18
import OrderedPartitions.ThreePoleTaylorData.Block19
import OrderedPartitions.ThreePoleTaylorData.Block20
import OrderedPartitions.ThreePoleTaylorData.Block21
import OrderedPartitions.ThreePoleTaylorData.Block22
import OrderedPartitions.ThreePoleTaylorData.Block23
import OrderedPartitions.ThreePoleTaylorData.Block24
import OrderedPartitions.ThreePoleTaylorData.Block25
import OrderedPartitions.ThreePoleTaylorData.Block26
import OrderedPartitions.ThreePoleData.All
namespace OrderedPartitions.ThreePoleCert
private theorem join (a b : List Cell) (x : a.all Cell.taylorPass = true) (y : b.all Cell.taylorPass = true) : (a++b).all Cell.taylorPass = true := by rw [List.all_append,x,y]; rfl

set_option maxHeartbeats 0 in
theorem all_taylor : cells.all Cell.taylorPass = true :=
  join rows00 (rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows00_taylor (join rows01 (rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows01_taylor (join rows02 (rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows02_taylor (join rows03 (rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows03_taylor (join rows04 (rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows04_taylor (join rows05 (rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows05_taylor (join rows06 (rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows06_taylor (join rows07 (rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows07_taylor (join rows08 (rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows08_taylor (join rows09 (rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows09_taylor (join rows10 (rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows10_taylor (join rows11 (rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows11_taylor (join rows12 (rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows12_taylor (join rows13 (rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows13_taylor (join rows14 (rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows14_taylor (join rows15 (rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows15_taylor (join rows16 (rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows16_taylor (join rows17 (rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows17_taylor (join rows18 (rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows18_taylor (join rows19 (rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows19_taylor (join rows20 (rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows20_taylor (join rows21 (rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) rows21_taylor (join rows22 (rows23 ++ rows24 ++ rows25 ++ rows26) rows22_taylor (join rows23 (rows24 ++ rows25 ++ rows26) rows23_taylor (join rows24 (rows25 ++ rows26) rows24_taylor (join rows25 (rows26) rows25_taylor (rows26_taylor))))))))))))))))))))))))))

#print axioms all_taylor
end OrderedPartitions.ThreePoleCert
