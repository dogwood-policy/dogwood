permit(
  principal in a::"\0\0\0\0\0B",
  action == Action::"",
  resource in a::"\0\0\0\0\0B"
) when {
  (true && ([].contains("cti"))) && false
};
