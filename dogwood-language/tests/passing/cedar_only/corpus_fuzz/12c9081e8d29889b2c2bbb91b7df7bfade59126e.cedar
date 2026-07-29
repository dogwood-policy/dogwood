@t("")
forbid(
  principal in a::"",
  action in [Action::"action"],
  resource in a::"\0\\^["
) when {
  (true && (((resource.getTag("")).getTag("")) is a)) && ((a::"\0\\^[".getTag("")) is a)
};
