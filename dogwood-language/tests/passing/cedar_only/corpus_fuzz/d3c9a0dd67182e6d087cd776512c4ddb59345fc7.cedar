permit(
  principal in a::"\0\0\0*",
  action,
  resource
) when {
  (true && (a::"\0\0\0*" has "")) && ((a::"\0\0\0*" has "") || (a::"\0\0\0*" has ""))
};
