forbid(
  principal is a,
  action == Action::"action",
  resource is a in a::"+\0"
) when {
  ((true && ((context["$"]) == ({"@": {}}["@"]))) && true) && false
};
