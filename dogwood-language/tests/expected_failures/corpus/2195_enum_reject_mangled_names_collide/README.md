# 2195_enum_reject_mangled_names_collide

`A_B::C` and `A::B_C` would both be exported as `A_B_C`, which would merge two different enums into one Cedar type. This depends only on `providers.json`, so loading the file fails.
