package kodkod.engine;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import kodkod.ast.Relation;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TemporalInstance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;

public class ElectrodProblemReader {
	
	static private List<Instance> insts = new ArrayList<Instance>();
	static private int loop = -1;
	static private Bounds bounds;
	
	static public TemporalInstance read(Bounds b, File file) throws ParserConfigurationException, SAXException, IOException {
		bounds = b;
		
	    DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
	    factory.setValidating(false);
	    factory.setIgnoringElementContentWhitespace(true);
	    DocumentBuilder builder = factory.newDocumentBuilder();
	    Document doc = builder.parse(file);
	    Element root = doc.getDocumentElement();
	    NodeList elems = root.getChildNodes();
	    int c = 0;
	    for (int i = 0; i < elems.getLength(); i++) {
	    	if (elems.item(i).getNodeName().equals("st")) {
	    		if (elems.item(i).getAttributes().getNamedItem("loop-target").getNodeValue().equals("true"))
	    			loop = c;
	    		insts.add(state(elems.item(i)));
	    		c++;
	    	}
	    }
		
		return null;
	}
	
	private static Instance state (Node node) {
		Instance inst = new Instance(bounds.universe());
		
		final TupleFactory f = bounds.universe().factory();
		
		// TODO: how to handle integers in unbounded problems?
		
		for(Relation r : bounds.relations()) {
			NodeList e = null;
		    for (int i = 0; i < node.getChildNodes().getLength(); i++) {
		    	if (node.getChildNodes().item(i).getNodeName().equals("rel")) {
		    		if (node.getChildNodes().item(i).getAttributes().getNamedItem("name").getNodeValue().equals(r.toString()))
		    			e = node.getChildNodes().item(i).getChildNodes();
		    	}
		    }
		    List<List<String>> buff__ = new ArrayList<List<String>>();

		    for (int i = 0; i < e.getLength(); i++) {
		    	if (e.item(i).getNodeName().equals("t")) {
				    List<String> buff_ = new ArrayList<String>();
				    for (int j = 0; j < e.item(i).getChildNodes().getLength(); j++) {
				    	if (e.item(i).getChildNodes().item(j).getNodeName().equals("a")) {
				    		buff_.add(e.item(i).getChildNodes().item(j).getTextContent());
				    	}
				    }
				    buff__.add(buff_);
		    	}
		    }
		    
		    List<Tuple> buff = new ArrayList<Tuple>();
		    for (List<String> buff_: buff__) {
		    	List<Object> _buff = new ArrayList<Object>();
			    for (String x: buff_)
				    for (int i = 0; i < bounds.universe().size(); i++) {
				    	if (bounds.universe().atom(i).toString().equals(x))
				    		_buff.add(bounds.universe().atom(i));
				    }
			    buff.add(bounds.universe().factory().tuple(_buff));
		    }
		    
		    TupleSet t = bounds.universe().factory().setOf(buff);
		    
			inst.add(r, t);
		}
		
		return inst;
	}

}
