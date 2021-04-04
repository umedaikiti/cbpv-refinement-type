'use strict';

import "./style.css";

interface Term {
	name: string;
	type: string;
	children: AST[];
}
interface Binder {
	name: string;
	type: string;
	child: AST;
}
type AST = { Term: Term; } | { Binder: Binder; };
interface Result {
	smtlib?: string | null;
	ast?: AST | null;
}

function create_ast_list(ast : AST) : HTMLElement {
	if("Term" in ast) {
		let name_type = document.createElement("span");
		name_type.appendChild(document.createTextNode(ast.Term.name + " : " + ast.Term.type));

		let children = document.createElement("ul");
		ast.Term.children.forEach((child) => {
			children.appendChild(create_ast_list(child));
		});
		if(ast.Term.children.length > 0) {
			children.classList.add("nested", "active");
			name_type.classList.add("caret", "caret-down");
			name_type.addEventListener("click", function() {
				this.parentElement.querySelector(".nested").classList.toggle("active");
				this.classList.toggle("caret-down");
			});
		}

		let li = document.createElement("li");
		li.appendChild(name_type);
		li.appendChild(children);
		return li;
	} else if("Binder" in ast) {
		let name_type = document.createElement("span");
		name_type.appendChild(document.createTextNode("[" + ast.Binder.name + " : " + ast.Binder.type + "]"));

		let children = document.createElement("ul");
		children.appendChild(create_ast_list(ast.Binder.child));

		let li = document.createElement("li");
		li.appendChild(name_type);
		li.appendChild(children);
		return li;
	}
	const _exhaustiveCheck: never = ast;
	console.log("error");
}

function show_result(result : Result) : void {
	let output = document.getElementById("output") as HTMLInputElement;
	let download = document.getElementById("download") as HTMLAnchorElement;
	if (result.smtlib === undefined || result.smtlib === null) {
		output.value = "";
		download.removeAttribute("href");
	} else {
		output.value = result.smtlib;
		let blob = new Blob([ result.smtlib ], { "type" : "text/plain" });;
		download.href = window.URL.createObjectURL(blob);
	}

	let ast_div = document.getElementById("ast");
	while(ast_div.firstChild) {
		ast_div.removeChild(ast_div.firstChild);
	}
	if (result.ast !== undefined && result.ast !== null) {
		let ast_list = document.createElement("ul");
		ast_list.setAttribute("style", "margin: 0; padding: 0;");
		ast_list.appendChild(create_ast_list(result.ast));
		ast_div.appendChild(ast_list);
	}
}

function getInput() {
	return document.getElementById("input") as HTMLInputElement;
}
function getSimplify() {
	return document.getElementById("simplify") as HTMLInputElement;
}

import("../pkg/").then(wasm => {
	wasm.init();

	let cbv_button = document.getElementById("cbv-button") as HTMLInputElement;
	cbv_button.disabled = false;
	cbv_button.addEventListener("click", function() {
		let result = wasm.to_smtlib_cbv(getInput().value, getSimplify().checked);
		show_result(result);
	});

	let cbn_button = document.getElementById("cbn-button") as HTMLInputElement;
	cbn_button.disabled = false;
	cbn_button.addEventListener("click", function() {
		let result = wasm.to_smtlib_cbn(getInput().value, getSimplify().checked);
		show_result(result);
	});
});

// set examples
const examples = require("./examples.json");
let select = document.getElementById("examples");
Object.keys(examples).forEach(key => {
	let example = document.createElement("option");
	example.setAttribute("value", key);
	example.innerHTML = key;
	select.appendChild(example);
});
select.addEventListener("change", (event) => {
	let key = (event.target as HTMLInputElement).value as keyof (typeof examples);
	getInput().value = examples[key];
});

