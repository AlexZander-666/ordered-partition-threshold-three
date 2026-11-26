import OrderedPartitions.ThreePoleFiniteRows

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def coeffs0 : Coeffs := [
  1
]
def boxes0 : Boxes := []
def history0 : List Coeffs := coeffs0 :: []

def coeffs1 : Coeffs := [
  1
]
def boxes1 : Boxes := []
def history1 : List Coeffs := coeffs1 :: history0

def coeffs2 : Coeffs := [
  3
]
def boxes2 : Boxes := []
def history2 : List Coeffs := coeffs2 :: history1

def coeffs3 : Coeffs := [
  12,
  1
]
def boxes3 : Boxes := [
  ((-3964585197,330382099),(-991146299,82595525))
]
def history3 : List Coeffs := coeffs3 :: history2

def coeffs4 : Coeffs := [
  66,
  9
]
def boxes4 : Boxes := [
  ((-3779571221,515396075),(-944892805,128849019))
]
def history4 : List Coeffs := coeffs4 :: history3

def coeffs5 : Coeffs := [
  450,
  91
]
def boxes5 : Boxes := [
  ((-3572523629,722443667),(-893130907,180610917))
]
def history5 : List Coeffs := coeffs5 :: history4

def coeffs6 : Coeffs := [
  3690,
  973,
  20
]
def boxes6 : Boxes := [
  ((-4200581407,94385889),(-2100290703,47192945)), ((-865072555,208669269),(-3460290219,834677077))
]
def history6 : List Coeffs := coeffs6 :: history5

def coeffs7 : Coeffs := [
  35280,
  11523,
  490
]
def boxes7 : Boxes := [
  ((-1022361317,51380507),(-4089445267,205522029)), ((-841253809,232488015),(-3365015235,929952061))
]
def history7 : List Coeffs := coeffs7 :: history6



end OrderedPartitions.ThreePoleFinite
