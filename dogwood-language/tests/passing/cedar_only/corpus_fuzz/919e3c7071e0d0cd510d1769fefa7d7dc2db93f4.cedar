@j531l555("")
permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && ((ip("\t\t\t\t\t\t\u{1}\u{7f}\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\u{2}\t\t\t\t\t\t\t\t\t\t[\t\t\0\0\0\0\0\0")).isLoopback())
};
