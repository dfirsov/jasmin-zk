#!/usr/bin/python3

# See "PARAMETERS and CONSTANTS" below for the configurable parts.

from dataclasses import dataclass
from pathlib import Path
from typing import List


@dataclass
class NLimbs:
    number: int
    val_op: str


@dataclass
class Constant:
    name: str
    value: int
    comment: str
    nlimbs: NLimbs

    def get_proc(self) -> str:
        assert self.value >= 0
        assert self.value < 2**(self.nlimbs.number * limb_size)
        proc_name = f"bn_set_{self.name}"
        lines = "\n".join([f"  {self.name}[{i}] = {(self.value // 2**(limb_size*i)) % 2**limb_size};"
                           for i in range(0, self.nlimbs.number)])
        return f"""/* Loads the {self.comment}. This function has the property (expressed as an Easycrypt lemma):

   op {self.name} : int = {self.value}.
   lemma {proc_name}_correct: phoare [ {proc_name} : true ==> {self.nlimbs.val_op} res = {self.name} ] = 1%r.
*/
inline fn {proc_name}(stack u64[nlimbs] {self.name}) -> stack u64[nlimbs] {{
{lines}
  return {self.name};
}}
"""


### PARAMETERS and CONSTANTS ###

nlimbs = NLimbs(number=32, val_op="W64xN.varR")
dnlimbs = NLimbs(number=nlimbs.number*2, val_op="W64x2N.varR")
limb_size: int = 64
output_file: str = "constants.jazz"

# MODP-2048 from RFC 3526, https://datatracker.ietf.org/doc/rfc3526
p = Constant(name="p", comment="modulus", nlimbs=nlimbs,
             value=32317006071311007300338913926423828248817941241140239112842009751400741706634354222619689417363569347117901737909704191754605873209195028853758986185622153212175412514901774520270235796078236248884246189477587641105928646099411723245426622522193230540919037680524235519125679715870117001058055877651038861847280257976054903569732561526167081339361799541336476559160368317896729073178384589680639671900977202194168647225871031411336429319536193471636533209717077448227988588565369208645296636077250268955505928362751121174096972998068410554359584866583291642136218231078990999448652468262416972035911852507045361090559)
q = Constant(name="q", comment="order of the generator", nlimbs=nlimbs,
             value = (p.value - 1) // 2)
g = Constant(name="g", comment="generator", nlimbs=nlimbs, value=2)
bp = Constant(name="bp", comment="barret parameter for p", nlimbs=dnlimbs,
              value = (4 ** (limb_size*nlimbs.number)) // p.value)
bq = Constant(name="bq", comment="barret parameter for q", nlimbs=dnlimbs,
              value = (4 ** (limb_size*nlimbs.number)) // q.value)

constants: List[Constant] = [p, q, g, bp, bq]



def main() -> None:
    assert Path("params.jinc").read_text().strip() == f"param int nlimbs = {nlimbs.number};"
    with open(output_file, "w") as f:
        f.write("/* This file is autogenerated by constants.py */\n")
        for const in constants:
            f.write("\n")
            f.write(const.get_proc())


if __name__ == '__main__':
    main()