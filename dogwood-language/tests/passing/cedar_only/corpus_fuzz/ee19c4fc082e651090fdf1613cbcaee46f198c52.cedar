@A("")
forbid(
  principal,
  action,
  resource
) when {
  (true && ((if ({"": false}[""]) then principal else principal) has "\0")) && true
};
