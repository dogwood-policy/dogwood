forbid(
  principal in a::"",
  action in [Action::"action"],
  resource is a
) when {
  true && ((if ((datetime("0606-06-2017:07:50-0838")) < (datetime("0000-01-01"))) then principal else principal) in principal)
};
