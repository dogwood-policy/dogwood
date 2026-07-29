forbid(
  principal is a in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a in a::""
) when {
  ((true && ((if ("" like "") then (if true then {"": {"": {"": {}}}} else {"": {"": {"": {}}}}) else (if false then context else {"": {"": {"": {}}}})) == (if ("" like "") then (if true then {"": {"": {"": {}}}} else context) else {"": context}))) && ((({"": {"|": {"": {"": {"": {}}}}}}[""])["|"]) == (({z: {"": {}}}.z)[""]))) && ((if ("" like "") then (if true then {"": {"": {"": {}}, "1": {"": {}}}, w3: {"": {"": {}}}} else {"": {"": {"": {}}, "1": {"": {}}}, w3: {"": {"": {}}}}) else {"": {"": {"": context}, "1": context}, w3: context}) == context)
};
