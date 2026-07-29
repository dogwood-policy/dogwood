permit(
  principal == a::"",
  action in [Action::"                            "],
  resource
) when {
  true && (a::"" in principal)
};
