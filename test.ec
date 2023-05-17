

require import ZModP Int AllCore List.
require SafeSubtype.

op p = 5.

clone SafeSubtype as STp
with type T = int, op P x = (0 <= x && x < p)
proof *.
realize inhabited.
  exists 0. by auto.
qed.

clone ZModP.ZModRing with
  type zmod = STp.sT, 
  op p = p,
  theory Sub = STp
proof *.
realize ge2_p. auto. qed.

section.
  declare type a.

  declare op x : int.
  abstract theory T.

    clone include Subtype
      with type T  <= a list,
           pred P  <= fun (xs : T) => size xs <= 5.
  end T.
end section.

print T.

lemma x: range 1 3.
