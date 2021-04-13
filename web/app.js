import React from 'react';
import ReactDOM from 'react-dom';
import { MoleculeProvider, Workbench } from 'molecule';
import 'molecule/esm/style/mo.css';
import { ExtendTestPane } from './extensions/test';

const App = () => (
	<MoleculeProvider extensions={[ExtendTestPane]}>
		<Workbench />
	</MoleculeProvider>
);

ReactDOM.render(<App />, document.getElementById('root'));
