forbid(
  principal in a::"\0\0*",
  action in [Action::"action"],
  resource is a in a::"\0\0*"
) when {
  ((true && ([{"": true, "00:": ""}, {"": false, "00:": ""}, context].contains(if (action in principal) then ({"on};": {"": true, "00:": ""}}["on};"]) else {"": true, "00": true, "00:": ""}))) && false) && false
};
