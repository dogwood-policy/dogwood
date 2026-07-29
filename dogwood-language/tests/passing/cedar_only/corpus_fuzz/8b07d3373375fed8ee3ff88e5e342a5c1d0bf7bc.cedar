permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && (a::"" in a::"")) && (a::"" == (((datetime("6977-08-08T07:07:00Z")).offset(duration("720576589657538314ms"))).offset(duration("720576589657538314ms"))))) && false
};
