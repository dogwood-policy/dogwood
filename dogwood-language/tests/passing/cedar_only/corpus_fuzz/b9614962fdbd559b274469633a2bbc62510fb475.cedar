forbid(
  principal == a::"",
  action == Action::"}}c",
  resource == a::""
) when {
  (true && (!(!true))) && (if (a::"" in resource) then ("MMMMMMMMMMMPMMMMM\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0>" like "") else ((if false then {} else {}) has "MMMMMMMMMMMPMMMMM\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0>"))
};
