@Af9fW0f("\u{7}A\u{f}")
@B("Aisi")
@r("")
permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && ((if false then (ip("sion\0?.")) else (if true then (ip("0.0.0.0/0")) else (ip("50.255.255.255/32")))).isLoopback())
};
