import React from 'react';
import ReactDOM from 'react-dom';
import { MoleculeProvider, Workbench } from 'molecule';
import 'molecule/esm/style/mo.css';

const App = () => (
	<MoleculeProvider>
		<Workbench />
	</MoleculeProvider>
);

ReactDOM.render(<App />, document.getElementById('root'));
