import OrderedPartitions.ThreePoleFiniteData.Raw032
import OrderedPartitions.ThreePoleFiniteVector

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def weights32 : Weights := [
  (1,32), (2,496),
  (3,4960), (4,35960),
  (5,201376), (6,906192),
  (7,3365856), (8,10518300),
  (9,28048800), (10,64512240),
  (11,129024480), (12,225792840),
  (13,347373600), (14,471435600),
  (15,565722720), (16,601080390),
  (17,565722720), (18,471435600),
  (19,347373600), (20,225792840),
  (21,129024480), (22,64512240),
  (23,28048800), (24,10518300),
  (25,3365856), (26,906192),
  (27,201376), (28,35960),
  (29,4960), (30,496),
  (31,32), (32,1)
]
theorem checkedWeights32 : weights32 = weights 32 := by decide +kernel
private theorem vectorOK32 : vectorOK 32 history31 weights32 coeffs32 = true := by
  decide +kernel
theorem checkedRow32 : rowOK 32 history31 weights32 coeffs32 = true :=
  vector_sound vectorOK32

def weights33 : Weights := [
  (1,33), (2,528),
  (3,5456), (4,40920),
  (5,237336), (6,1107568),
  (7,4272048), (8,13884156),
  (9,38567100), (10,92561040),
  (11,193536720), (12,354817320),
  (13,573166440), (14,818809200),
  (15,1037158320), (16,1166803110),
  (17,1166803110), (18,1037158320),
  (19,818809200), (20,573166440),
  (21,354817320), (22,193536720),
  (23,92561040), (24,38567100),
  (25,13884156), (26,4272048),
  (27,1107568), (28,237336),
  (29,40920), (30,5456),
  (31,528), (32,33),
  (33,1)
]
theorem checkedWeights33 : weights33 = weights 33 := by decide +kernel
private theorem vectorOK33 : vectorOK 33 history32 weights33 coeffs33 = true := by
  decide +kernel
theorem checkedRow33 : rowOK 33 history32 weights33 coeffs33 = true :=
  vector_sound vectorOK33

def weights34 : Weights := [
  (1,34), (2,561),
  (3,5984), (4,46376),
  (5,278256), (6,1344904),
  (7,5379616), (8,18156204),
  (9,52451256), (10,131128140),
  (11,286097760), (12,548354040),
  (13,927983760), (14,1391975640),
  (15,1855967520), (16,2203961430),
  (17,2333606220), (18,2203961430),
  (19,1855967520), (20,1391975640),
  (21,927983760), (22,548354040),
  (23,286097760), (24,131128140),
  (25,52451256), (26,18156204),
  (27,5379616), (28,1344904),
  (29,278256), (30,46376),
  (31,5984), (32,561),
  (33,34), (34,1)
]
theorem checkedWeights34 : weights34 = weights 34 := by decide +kernel
private theorem vectorOK34 : vectorOK 34 history33 weights34 coeffs34 = true := by
  decide +kernel
theorem checkedRow34 : rowOK 34 history33 weights34 coeffs34 = true :=
  vector_sound vectorOK34

def weights35 : Weights := [
  (1,35), (2,595),
  (3,6545), (4,52360),
  (5,324632), (6,1623160),
  (7,6724520), (8,23535820),
  (9,70607460), (10,183579396),
  (11,417225900), (12,834451800),
  (13,1476337800), (14,2319959400),
  (15,3247943160), (16,4059928950),
  (17,4537567650), (18,4537567650),
  (19,4059928950), (20,3247943160),
  (21,2319959400), (22,1476337800),
  (23,834451800), (24,417225900),
  (25,183579396), (26,70607460),
  (27,23535820), (28,6724520),
  (29,1623160), (30,324632),
  (31,52360), (32,6545),
  (33,595), (34,35),
  (35,1)
]
theorem checkedWeights35 : weights35 = weights 35 := by decide +kernel
private theorem vectorOK35 : vectorOK 35 history34 weights35 coeffs35 = true := by
  decide +kernel
theorem checkedRow35 : rowOK 35 history34 weights35 coeffs35 = true :=
  vector_sound vectorOK35

def weights36 : Weights := [
  (1,36), (2,630),
  (3,7140), (4,58905),
  (5,376992), (6,1947792),
  (7,8347680), (8,30260340),
  (9,94143280), (10,254186856),
  (11,600805296), (12,1251677700),
  (13,2310789600), (14,3796297200),
  (15,5567902560), (16,7307872110),
  (17,8597496600), (18,9075135300),
  (19,8597496600), (20,7307872110),
  (21,5567902560), (22,3796297200),
  (23,2310789600), (24,1251677700),
  (25,600805296), (26,254186856),
  (27,94143280), (28,30260340),
  (29,8347680), (30,1947792),
  (31,376992), (32,58905),
  (33,7140), (34,630),
  (35,36), (36,1)
]
theorem checkedWeights36 : weights36 = weights 36 := by decide +kernel
private theorem vectorOK36 : vectorOK 36 history35 weights36 coeffs36 = true := by
  decide +kernel
theorem checkedRow36 : rowOK 36 history35 weights36 coeffs36 = true :=
  vector_sound vectorOK36

def weights37 : Weights := [
  (1,37), (2,666),
  (3,7770), (4,66045),
  (5,435897), (6,2324784),
  (7,10295472), (8,38608020),
  (9,124403620), (10,348330136),
  (11,854992152), (12,1852482996),
  (13,3562467300), (14,6107086800),
  (15,9364199760), (16,12875774670),
  (17,15905368710), (18,17672631900),
  (19,17672631900), (20,15905368710),
  (21,12875774670), (22,9364199760),
  (23,6107086800), (24,3562467300),
  (25,1852482996), (26,854992152),
  (27,348330136), (28,124403620),
  (29,38608020), (30,10295472),
  (31,2324784), (32,435897),
  (33,66045), (34,7770),
  (35,666), (36,37),
  (37,1)
]
theorem checkedWeights37 : weights37 = weights 37 := by decide +kernel
private theorem vectorOK37 : vectorOK 37 history36 weights37 coeffs37 = true := by
  decide +kernel
theorem checkedRow37 : rowOK 37 history36 weights37 coeffs37 = true :=
  vector_sound vectorOK37

def weights38 : Weights := [
  (1,38), (2,703),
  (3,8436), (4,73815),
  (5,501942), (6,2760681),
  (7,12620256), (8,48903492),
  (9,163011640), (10,472733756),
  (11,1203322288), (12,2707475148),
  (13,5414950296), (14,9669554100),
  (15,15471286560), (16,22239974430),
  (17,28781143380), (18,33578000610),
  (19,35345263800), (20,33578000610),
  (21,28781143380), (22,22239974430),
  (23,15471286560), (24,9669554100),
  (25,5414950296), (26,2707475148),
  (27,1203322288), (28,472733756),
  (29,163011640), (30,48903492),
  (31,12620256), (32,2760681),
  (33,501942), (34,73815),
  (35,8436), (36,703),
  (37,38), (38,1)
]
theorem checkedWeights38 : weights38 = weights 38 := by decide +kernel
private theorem vectorOK38 : vectorOK 38 history37 weights38 coeffs38 = true := by
  decide +kernel
theorem checkedRow38 : rowOK 38 history37 weights38 coeffs38 = true :=
  vector_sound vectorOK38

def weights39 : Weights := [
  (1,39), (2,741),
  (3,9139), (4,82251),
  (5,575757), (6,3262623),
  (7,15380937), (8,61523748),
  (9,211915132), (10,635745396),
  (11,1676056044), (12,3910797436),
  (13,8122425444), (14,15084504396),
  (15,25140840660), (16,37711260990),
  (17,51021117810), (18,62359143990),
  (19,68923264410), (20,68923264410),
  (21,62359143990), (22,51021117810),
  (23,37711260990), (24,25140840660),
  (25,15084504396), (26,8122425444),
  (27,3910797436), (28,1676056044),
  (29,635745396), (30,211915132),
  (31,61523748), (32,15380937),
  (33,3262623), (34,575757),
  (35,82251), (36,9139),
  (37,741), (38,39),
  (39,1)
]
theorem checkedWeights39 : weights39 = weights 39 := by decide +kernel
private theorem vectorOK39 : vectorOK 39 history38 weights39 coeffs39 = true := by
  decide +kernel
theorem checkedRow39 : rowOK 39 history38 weights39 coeffs39 = true :=
  vector_sound vectorOK39


#print axioms checkedRow39

end OrderedPartitions.ThreePoleFinite
