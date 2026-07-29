@r("")
permit(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  ((true && ("\0ʐ" like "\0*ʐ*")) && ("\0ʐ" like "\0*ʐ*")) && ("\0ʐ" like "\0*ʐ*")
};
