permit(
  principal == a::"\0\0\0\0",
  action,
  resource
) when {
  true && ((if (action in action) then a::"\0\0\0\0" else (if false then action else action)) in a::"\0\0\0\0")
};
