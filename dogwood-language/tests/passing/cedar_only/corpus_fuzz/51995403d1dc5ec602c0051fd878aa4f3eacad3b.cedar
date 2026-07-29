permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && ((if false then (ip("sion\0?.")) else (if true then (ip("0.0.0.0/00")) else (ip("::49:4949:4949:4949:4949:4949")))).isLoopback())
};
