#!/usr/bin/python3
from pathlib import Path
from typing import List, Tuple

nlimbs: int = 32
limb_size: int = 64
output_file: str = "constants.jazz"

constants: List[Tuple[str, int, str]] = [
    ('p', 123456789012345678901234567890, 'modulus'),
    ('q', 2**64, 'order of the generator'),
    ('g', 2, 'generator')
]


def main() -> None:
    assert Path("params.jinc").read_text().strip() == f"param int nlimbs = {nlimbs};"
    with open(output_file, "w") as f:
        f.write("/* This file is autogenerated by constants.py */\n")
        for const_name, const_value, comment in constants:
            proc_name = f"bn_set_{const_name}"
            assert const_value >= 0
            assert const_value < 2**(nlimbs*limb_size)
            lines = "\n".join([f"  {const_name}[{i}] = {(const_value // 2**(limb_size*i)) % 2**limb_size};" for i in range(0,nlimbs)])
            f.write(f"""
/* Loads the {comment}. This function has the property:

   op {const_name} : int = {const_value}.
   lemma {proc_name}_correct: hoare [ {proc_name} : true ==> as_int res = {const_name} ].
*/
inline fn bn_set_gg(stack u64[nlimbs] {const_name}) -> stack u64[nlimbs] {{
{lines}
}}
return {const_name}
""")


if __name__ == '__main__':
    main()
