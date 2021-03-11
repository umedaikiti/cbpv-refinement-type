import("../pkg/").then(js => {
//	js.greet("test");
	const examples = require("./examples.json");
	let select = document.getElementById("examples");
	Object.keys(examples).forEach(key => {
		let example = document.createElement("option");
		example.setAttribute("value", key);
		example.innerHTML = key;
		select.appendChild(example);
	});
	select.addEventListener("change", (event) => {
		document.getElementById("input").value = examples[event.target.value];
	});
	document.getElementById("cbv-button").addEventListener("click", function() {
		let input = document.getElementById("input");
		let result = js.to_smtlib_cbv(input.value);
		let output = document.getElementById("output");
		if (result === undefined) {
			output.value = "";
		} else {
			output.value = result;
		}
	});
	document.getElementById("cbn-button").addEventListener("click", function() {
		let input = document.getElementById("input");
		let result = js.to_smtlib_cbn(input.value);
		let output = document.getElementById("output");
		if (result === undefined) {
			output.value = "";
		} else {
			output.value = result;
		}
	});
});
