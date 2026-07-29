permit(
  principal == a::"",
  action in [],
  resource in a::""
) when {
  ((true && ("////////" like "/*/*/*/*/*/*")) && ("////////" like "/*/*/*/*/*/*")) && ("////////" like "/**/*/*/*//")
};
